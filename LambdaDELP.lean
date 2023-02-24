import init.data.set 

section List 
  inductive List (α : Type)
  | nil : List
  | cons : α → List → List

  def List.mem {α : Type} (a : α) : List α → Prop
  | List.nil := false
  | (List.cons b l) := a = b ∨ List.mem l

  notation x ` ∈κ ` xs := List.mem x xs 

  theorem List.mem_cons_of_mem {α : Type} {a b : α} {l : List α} (h : a ∈κ l) :
    a ∈κ (List.cons b l) := 
    begin 
      exact or.inr h
    end  

  theorem List.mem_cons_self {α : Type } (a : α) (l : List α) : a ∈κ List.cons a l :=
    or.inl rfl

  theorem List.mem_nil {α : Type} (a : α) : ¬ (List.mem a List.nil) := λ h, h

  notation `[]` := List.nil 
  infixr `::` := List.cons

  def List.append {α : Type} : List α → List α → List α
  | List.nil ys := ys
  | (List.cons x xs) ys := List.cons x (List.append xs ys)

  notation xs `++` ys := List.append xs ys
  
  def A : List ℕ := 3 :: 4 :: 5 :: [] 
  def B : List ℕ := 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: []

  @[simp]
  def List.subset { α : Type } (A : List α) (B : List α) : Prop := ∀ x : α, ((x ∈κ A) -> (x ∈κ B))

  notation A ` ⊆κ ` B := List.subset A B 

  example : A ⊆κ B := 
    begin 
      intro x, 
      intro ha, 
      cases ha, 
      { rw [ha], 
        repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem } 
      },
      {
          cases ha, 
          { rw [ha], 
            repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem } 
          },
          {
            cases ha, 
            { rw [ha], 
              repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem } 
            },
            {
              cases ha
            }
          }
      }
    end 

    
end List 

-- language -- 
inductive message (σ : ℕ) : Type 
  | null : fin σ -> message 
  | conc : message -> message -> message 
  | nonc : message -> message 
  | pk : message -> message
  | sk : message -> message 
  | keys : message -> message -> message -> message 
  | encr : message -> message -> message
  | decr : message -> message -> message
  | tupl : message -> message -> message 
  | func : message -> message -> message 

inductive program (σ : ℕ) : Type 
  | skip : program 
  | secv : program -> program -> program 
  | reun : program -> program -> program 
  | send : program 
  | recv : program 
  | star : program -> program 
  | agP : program -> message σ -> message σ -> program 

inductive form (σ : ℕ) : Type 
  | atom : fin σ -> form 
  | botm : form 
  | impl : form -> form -> form 
  | k : message σ -> form -> form 
  | b : message σ -> form -> form 
  | pdl : program σ -> message σ → message σ → form -> form 
  | receive : program σ -> message σ -> form -> form  
  | toP : program σ -> form -> form 
  | mesg : message σ -> form 
  | awareness : message σ -> form -> form 
  | explicit : message σ -> form -> form 


section Notations 
  prefix `#` := form.atom 
  notation `⊥` := form.botm
  infix `⊃` := form.impl 
  notation `~`:40 p := form.impl p ⊥ 
  notation p `&` q := ~(p ⊃ (~q))
  notation p `or` q := ~((~p) & (~q))
  notation `K`:80 m `,` p := form.k m p 
  notation `E`:80 m `,` p := form.awareness m p 
  notation `X`:80 m `,` p := form.explicit m p 
  notation `B`:80 m `,` p := form.b m p 
  notation `[` α ` : ` i ` , ` j ` ] `:80  p := form.pdl α i j p 
  notation `[` α ` : ` i ` ] `:80  p := form.receive α i p 
  notation `[` α `]`:80 p := form.toP α p 
  notation α `*`:80 := program.star α 
  notation `ι` m := form.mesg m 
  notation α `;` β := program.secv α β 
end Notations 

@[reducible]
def ctx (σ : nat) : Type := List (form σ)

@[reducible]
def constCtx (σ : nat) : Type := List (message σ)


/-
  Proof system 
-/

open form 
open message
open program 
open List 

section ProofSystem 
  inductive Proof { σ : ℕ } : ctx σ → constCtx σ → form σ → Prop 
  -- Propositional logic
  | ax { Λ } { ℂ : constCtx σ } { p : form σ } (h : p ∈κ Λ) : Proof Λ ℂ p  
  | pl1 { Λ } { ℂ : constCtx σ } { p q : form σ } : Proof Λ ℂ (p ⊃ (q ⊃ p))
  | pl2 { Λ } { ℂ : constCtx σ } { p q r : form σ } : Proof Λ ℂ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
  | pl3 { Λ } { ℂ : constCtx σ } { p q } : Proof Λ ℂ (((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p))
  | andelim₁ { Λ } { ℂ : constCtx σ } { p q } (hp : Proof Λ ℂ (p & q)) : Proof Λ ℂ p
  | andelim₂ { Λ } { ℂ : constCtx σ } { p q } (hp : Proof Λ ℂ (p & q)) : Proof Λ ℂ q 
  | andintro { Λ } { ℂ : constCtx σ } { p q } (hp : Proof Λ ℂ p) (hq : Proof Λ ℂ q ) : Proof Λ ℂ (p & q) 
  | trans { Λ } { ℂ : constCtx σ } { p q r : form σ } (hp : Proof Λ ℂ (p ⊃ q)) (hq: Proof Λ ℂ (q ⊃ r)) : Proof Λ ℂ (p ⊃ r)
  -- S5
  | kk { Λ } { ℂ : constCtx σ } { i : message σ } { p q } : Proof Λ ℂ (K i, (p ⊃ q) ⊃ (K i, p ⊃ K i, q))
  | t { Λ } { ℂ : constCtx σ } { i : message σ } { p } : Proof Λ ℂ ((K i, p) ⊃ p) 
  | s4 { Λ } { ℂ : constCtx σ } { i : message σ } { p } : Proof Λ ℂ (K i, p ⊃ K i, K i, p) 
  -- KD
  | bk { Λ } { ℂ : constCtx σ } { i : message σ } { p q } : Proof Λ ℂ ((B i, (p ⊃ q)) ⊃ ((B i, p) ⊃ (B i, q)))
  | dox { Λ } { ℂ : constCtx σ } { i : message σ } { p } : Proof Λ ℂ (B i, p ⊃ ~B i, (~p))
  | kb { Λ } { ℂ : constCtx σ } { i : message σ } { p } : Proof Λ ℂ ((K i, p) ⊃ (B i, p))
  -- PDL
  | pdlk { Λ } { ℂ : constCtx σ } { i j : message σ } { p q } (α : program σ) : Proof Λ ℂ (([α : i, j](p ⊃ q)) ⊃ ([α : i, j]p  ⊃ [α : i, j] q))
  | pdt { Λ } { ℂ : constCtx σ } { i j : message σ } { p : form σ } {α : program σ } : Proof Λ ℂ (([α : i, j] p) ⊃ p)
  -- PDL*
  | pdlstar₁ { Λ } { ℂ : constCtx σ } { φ : form σ } { α : program σ } (h : Proof Λ ℂ (φ & [α][α*]φ)) : Proof Λ ℂ ([α*]φ)
  | pdlstar₂ { Λ } { ℂ : constCtx σ } { φ : form σ } { α : program σ } (h : Proof Λ ℂ (φ & [α*](φ ⊃ [α]φ))) : Proof Λ ℂ ([α*]φ)
  -- Deductive rules 
  | mp { Λ } { ℂ : constCtx σ } { p q } (hpq: Proof Λ ℂ (p ⊃ q)) (hp : Proof Λ ℂ p) : Proof Λ ℂ q
  | knec { Λ } { ℂ : constCtx σ } { i : message σ } { p } (h : Proof [] ℂ p) : Proof Λ ℂ (K i, p)
  | bnec { Λ } { ℂ : constCtx σ } { p } { i : message σ } (h : Proof Λ ℂ p) : Proof Λ ℂ (B i, p)
  | gen { Λ } { ℂ : constCtx σ } { p } { i j : message σ } (α : program σ) (h : Proof Λ ℂ p) : Proof Λ ℂ ([α : i, j]p)
  -- theory of modal constants 
  | c₁left { Λ } { ℂ : constCtx σ } { i m₁ m₂ : message σ} 
    (h₁ : m₁ ∈κ ℂ) 
    (h₂ : m₂ ∈κ ℂ) 
    (hp₁ : Proof Λ ℂ (K i, ι m₁)) 
    (hp₂ : Proof Λ ℂ (K i, ι m₂))
    : Proof Λ ℂ (K i, (ι m₁.conc m₂))
  | c₁right₁ { Λ } { ℂ : constCtx σ } { i m₁ m₂ : message σ} 
    (h₁ : m₁ ∈κ ℂ) 
    (h₂ : m₂ ∈κ ℂ) 
    (hp : Proof Λ ℂ (K i, (ι m₁.conc m₂)))
    : Proof Λ ℂ (K i, ι m₁) 
  | c₁right₂ { Λ } { ℂ : constCtx σ } { i m₁ m₂ : message σ} 
    (h₁ : m₁ ∈κ ℂ) 
    (h₂ : m₂ ∈κ ℂ) 
    (hp : Proof Λ ℂ (K i, (ι m₁.conc m₂)))
    : Proof Λ ℂ (K i, ι m₂)
  | c₂ { Λ } { ℂ : constCtx σ } { k j l : message σ }
    (h : (k.keys j l) ∈κ ℂ)
    : Proof Λ ℂ (ι k.keys l j)
  | c₃ { Λ } { ℂ : constCtx σ } { i j m : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (K i, ι m.encr j.pk))
    (hp₂ : Proof Λ ℂ (K i, ι j.sk))
    : Proof Λ ℂ (K i, ι m)
  | c₄ { Λ } { ℂ : constCtx σ } { i j m : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (K i, ι m.encr j.sk))
    (hp₂ : Proof Λ ℂ (K i, ι j.pk))
    : Proof Λ ℂ (K i, ι m)
  | c₅ { Λ } { ℂ : constCtx σ } {i m k : message σ }
    (h₁ : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (K i, ι m))
    (hp₂ : Proof Λ ℂ (K i, ι k))
    : Proof Λ ℂ (K i, ι m.encr k)
  | c₆ { Λ } { ℂ : constCtx σ } { i j k l m : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (K i, ι m.encr k))
    (hp₂ : Proof Λ ℂ (K i, ι k.keys j l))
    : Proof Λ ℂ (K i, ι m)
  -- awareness 
  | e₁left₁ { Λ } { ℂ : constCtx σ } { i m₁ m₂ : message σ }
    (h₁ : m₁ ∈κ ℂ)
    (h₂ : m₂ ∈κ ℂ)
    (hp : Proof Λ ℂ (E i, (ι m₁.conc m₂)))
    : Proof Λ ℂ (E i, ι m₁)
  | e₁left₂ { Λ } { ℂ : constCtx σ } { i m₁ m₂ : message σ }
    (h₁ : m₁ ∈κ ℂ)
    (h₂ : m₂ ∈κ ℂ)
    (hp : Proof Λ ℂ (E i, (ι m₁.conc m₂)))
    : Proof Λ ℂ (E i, ι m₂)
  | e₂right { Λ } { ℂ : constCtx σ } { i m₁ m₂ : message σ }
    (h₁ : m₁ ∈κ ℂ)
    (h₂ : m₂ ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (E i, ι m₁))
    (hp₂ : Proof Λ ℂ (E i, ι m₂))
    : Proof Λ ℂ (E i, (ι m₁.conc m₂))
  | e₂ { Λ } { ℂ : constCtx σ } { i j k l : message σ }
    (h : k ∈κ ℂ)
    (hp : Proof Λ ℂ (E i, ι k.keys j l))
    : Proof Λ ℂ (E i, ι k.keys l j)
  | e₃ { Λ } { ℂ : constCtx σ } { i j m : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (E i, ι m.encr (j.pk)))
    (hp₂ : Proof Λ ℂ (E i, ι (j.sk)))
    : Proof Λ ℂ (E i, ι m)
  | e₄ { Λ } { ℂ : constCtx σ } { i j m : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (E i, ι m.encr (j.sk)))
    (hp₂ : Proof Λ ℂ (E i, ι (j.pk)))
    : Proof Λ ℂ (E i, ι m)
  | e₅ { Λ } { ℂ : constCtx σ } { i m k : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (E i, ι m))
    (hp₂ : Proof Λ ℂ (E i, ι k))
    : Proof Λ ℂ (E i, ι m.encr k)
  | e₆ { Λ } { ℂ : constCtx σ } { i j k l m : message σ }
    (h : m ∈κ ℂ)
    (hp₁ : Proof Λ ℂ (E i, ι m.encr k))
    (hp₂ : Proof Λ ℂ (E i, ι k.keys j l))
    : Proof Λ ℂ (E i, ι m)
  -- explicit knowledge 
  | explicit₁₀ { Λ } { ℂ : constCtx σ } { i m : message σ } 
    : Proof Λ ℂ ((X i, ι m) ⊃ (K i, ι m))
  | explicit₁₁ { Λ } { ℂ : constCtx σ } { i m : message σ } 
    (h : Proof Λ ℂ (X i, ι m))
    : Proof Λ ℂ (K i, ι m)
  | explicit₁₂ { Λ } { ℂ : constCtx σ } { i m : message σ } 
    (h : Proof Λ ℂ (X i, ι m))
    : Proof Λ ℂ (E i, ι m)
  | explicit₂ { Λ } { ℂ : constCtx σ } { i m : message σ } 
    (h₁ : Proof Λ ℂ (K i, ι m))
    (h₂ : Proof Λ ℂ (E i, ι m))
    : Proof Λ ℂ (X i, ι m)
  -- axioms for protocols 
  | H₀₀ { Λ } { ℂ : constCtx σ } { i j m : message σ }  
    : Proof Λ ℂ (([send : i, j] (ι m)) ⊃ ([recv : j] (ι m)))
  | H₀ { Λ } { ℂ : constCtx σ } { i j m : message σ } 
    (h : Proof Λ ℂ ([send : i, j] (ι m)))
    : Proof Λ ℂ ([recv : j] (ι m))
  | H₁₀ { Λ } { ℂ : constCtx σ } { i j m : message σ } 
    : Proof Λ ℂ (([send : i, j] ι m) ⊃ (X i, ι m)) 
  | H₁ { Λ } { ℂ : constCtx σ } { i j m : message σ }
    (hp : Proof Λ ℂ ([send : i, j] ι m))
    : Proof Λ ℂ (X i, ι m)
  | H₂₀ { Λ } { ℂ : constCtx σ } { i m : message σ }
    : Proof Λ ℂ (([recv : i] ι m) ⊃ (X i, ι m))
  | H₂ { Λ } { ℂ : constCtx σ } { i m : message σ }
    (hp : Proof Λ ℂ ([recv : i] ι m))
    : Proof Λ ℂ (X i, ι m)
end ProofSystem

notation Λ `-` ℂ ` ⊢κ ` p := Proof Λ ℂ p

open Proof 

variable { σ : nat }
variable { p : form σ }

theorem extension_is_consistent { σ : ℕ } { Λ : ctx σ } { Λ' : ctx σ } { ℂ : constCtx σ } { φ : form σ }
  (h₁ : φ ∈κ Λ)
  (h₂ : Λ ⊆κ Λ')
  : Λ'-ℂ ⊢κ φ := 
  begin 
    simp [List.subset] at h₂,
    specialize h₂ φ,
    have h₃ := h₂ h₁,
    exact ax h₃ 
  end 

section OSS 
  /-
    OSS Theory 
  -/

  variables { i r ni : message σ }

  def OSSPK₁₁ : form σ := (X i, ((ι r.pk) & (ι i.pk)))
  def OSSPK₁₂ : form σ := (X r, ((ι r.pk) & (ι i.pk)))
  def OSSPK₂₁ : form σ := (X i, ι i.sk) 
  def OSSPK₂₂ : form σ := (X r, ι r.sk)
  def OSS : form σ := ([send : i, r] (ι ((i.conc ni).encr (r.pk))))
  def OSSI : form σ := (X i, ι ni) 
  def OSSB : form σ := (([recv : r] (ι (i.conc ni).encr (r.pk))) 
    ⊃ ((B r, [send : i, r] ι ((i.conc ni).encr (r.pk))) & (B r, (X i, ι ni))))

  def ΛOSS : ctx σ := (@OSS σ i r ni) :: (@OSSI σ i ni) :: (@OSSB σ i r ni) 
    :: (@OSSPK₁₁ σ i r) :: (@OSSPK₁₂ σ i r) :: (@OSSPK₂₁ σ i) :: (@OSSPK₂₂ σ r) :: [] 
  def ℂOSS : constCtx σ := ni :: (i.conc ni) :: i :: []  

  theorem OSS_r_knows_ni { σ : nat } { i r ni : message σ } 
    : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ X r, ι ni := 
    begin 
      have pk₁₂ : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ (X r, ((ι r.pk) & (ι i.pk))) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
      have pk₂₂ : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ (X r, ι r.sk) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }), 
      have oss : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ ([send : i, r] (ι ((i.conc ni).encr (r.pk)))) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }), 
      have h₁ := c₃ (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }) 
        (explicit₁₁ (H₂ (H₀ oss))) 
        (explicit₁₁ pk₂₂),  
      have h₂ : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ E r, ι (i.conc ni) := e₃ 
        (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }) 
        (explicit₁₂ (H₂ (H₀ oss))) 
        (explicit₁₂ pk₂₂), 
      have h₃ := @c₁right₂ σ (@ΛOSS σ i r ni) (@ℂOSS σ i ni) 
        r i ni 
        (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }) 
        (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }) 
        h₁,
      have h₄ := @e₁left₂ σ (@ΛOSS σ i r ni) (@ℂOSS σ i ni) 
        r i ni 
        (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }) 
        (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }) 
        h₂, 
        exact explicit₂ h₃ h₄,
    end 

  theorem OSS_r_believes_i_knows_ni { σ : nat } { i r ni : message σ } 
    : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ B r, (X i, ι ni) :=
    begin 
      have oss : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ ([send : i, r] (ι ((i.conc ni).encr (r.pk)))) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }), 
      have ossb : (@ΛOSS σ i r ni)-(@ℂOSS σ i ni) ⊢κ (([recv : r] (ι (i.conc ni).encr (r.pk))) 
        ⊃ ((B r, [send : i, r] ι ((i.conc ni).encr (r.pk))) & (B r, (X i, ι ni)))) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
      exact andelim₂ (mp ossb (H₀ oss))
    end

  /-
    Attack in OSS 
  -/
  variables { e ne : message σ }
  def ATT : form σ := (((X e, ι ne) & ~(X i, ι ne)) & [send : e, r] ι (i.conc ne).encr (r.pk))
  def OSSBATT : form σ := (([recv : r] (ι (i.conc ne).encr (r.pk))) 
    ⊃ ((B r, [send : i, r] ι ((i.conc ne).encr (r.pk))) & (B r, (X i, ι ne))))

  def ΛOSSATT : ctx σ := (@ΛOSS σ i r ni) ++ ((@ATT σ i r e ne) :: (@OSSBATT σ i r ne) :: [])
  def ℂOSSATT : constCtx σ := (@ℂOSS σ i ni) ++ (e :: ne :: [])

  theorem OSS_attack { σ : nat } { i r ni e ne : message σ }
    : (@ΛOSSATT σ i r ni e ne)-(@ℂOSSATT σ i ni e ne) ⊢κ (B r, [send : i, r] ι ((i.conc ne).encr (r.pk)) & (B r, (X i, ι ne))) := 
    begin 
      have ossatt : (@ΛOSSATT σ i r ni e ne)-(@ℂOSSATT σ i ni e ne) ⊢κ 
        (((X e, ι ne) & ~(X i, ι ne)) & [send : e, r] ι (i.conc ne).encr (r.pk)) := 
          ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
        have ossb : (@ΛOSSATT σ i r ni e ne)-(@ℂOSSATT σ i ni e ne) ⊢κ (([recv : r] (ι (i.conc ne).encr (r.pk))) 
          ⊃ ((B r, [send : i, r] ι ((i.conc ne).encr (r.pk))) & (B r, (X i, ι ne)))) := 
          ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
        exact mp ossb (H₀ (andelim₂ ossatt)), 
    end 

end OSS 


section NeedhamSchroeder
  /-
    Needham-Schroeder 
  -/
  def agent := message 

  variables { i r n₁ n₂ : message σ }

  def NSPK₁₁ : form σ := (X i, ι i.pk)
  def NSPK₁₂ : form σ := (X i, ι i.sk)
  def NSPK₁₃ : form σ := (X i, ι r.pk)

  def NSPK₂₁ : form σ := (X r, ι r.pk)
  def NSPK₂₂ : form σ := (X r, ι r.sk)
  def NSPK₂₃ : form σ := (X r, ι i.pk)

  def NS₁ : form σ := (((X r, ι (i.conc n₁).encr (r.pk)) & (X r, ι n₂)) ⊃ [send : r, i] ι ((n₁.conc n₂).encr (i.pk)))
  def NS₂ : form σ := ((((X i, ι n₁) & ([send : i, r] ι (i.conc n₁).encr (r.pk))) & (X i, ι (n₁.conc n₂))) ⊃ [send : i, r] ι (n₂.encr (r.pk)))
  def NS₃ : form σ := (([recv : r] ι (i.conc n₁).encr (r.pk)) ⊃ ((B r, [send : i, r] ι ((i.conc n₁).encr (r.pk))) & (B r, (X i, ι n₁))))
  def NS₄ : form σ := ((((X i, ι n₁) & ([send : i, r] ι (i.conc n₁).encr (r.pk))) & ([recv : i] ι (n₁.conc n₂).encr (i.pk))) ⊃ ((B i, [send : r, i] ι ((n₁.conc n₂).encr (i.pk))) & (B i, (X r, ι n₂))))
  def NS₅ : form σ := ((((X r, ι n₂) & ([send : r, i] ι ((n₁.conc n₂).encr (i.pk)))) & ([recv : r] ι (n₂.encr (r.pk)))) ⊃ (B r, (X i, ι n₂)))

  def NSI₁ : form σ := (X i, ι n₁) 
  def NSI₂ : form σ := (X r, ι n₂)
  def NSI₃ : form σ := ([send : i, r] ι ((i.conc n₁).encr (r.pk)))

  def ΛNSPK : ctx σ := (@NSPK₁₁ σ i) :: (@NSPK₁₂ σ i) :: (@NSPK₁₃ σ i r)
    :: (@NSPK₂₁ σ r) :: (@NSPK₂₂ σ r) :: (@NSPK₂₃ σ i r) 
    :: (@NS₁ σ i r n₁ n₂) :: (@NS₂ σ i r n₁ n₂) :: (@NS₃ σ i r n₁) :: (@NS₄ σ i r n₁ n₂) :: (@NS₅ σ i r n₁ n₂)
    :: (@NSI₁ σ i n₁) :: (@NSI₂ σ r n₂) :: (@NSI₃ σ i r n₁) :: [] 

  def C₁ : message σ := ((i.conc n₁))

  def ℂNSPK : constCtx σ := (@C₁ σ i n₁) :: (i) :: (n₁) :: []


  theorem NSPK_Xr_ni { σ : nat } { i r n₁ n₂ : message σ } 
    : (@ΛNSPK σ i r n₁ n₂)-(@ℂNSPK σ i n₁) ⊢κ X r, ι n₁ := 
  begin 
    have nsi₃ : (@ΛNSPK σ i r n₁ n₂)-(@ℂNSPK σ i n₁) ⊢κ ([send : i, r] ι ((i.conc n₁).encr (r.pk))) := 
      ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
    have h₁ := H₂ (H₀ nsi₃),
    have nspk₂₂ :  (@ΛNSPK σ i r n₁ n₂)-(@ℂNSPK σ i n₁) ⊢κ (X r, ι r.sk) := 
      ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
    have h₂ := c₃ ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) (explicit₁₁ h₁) (explicit₁₁ nspk₂₂),
    have h₃ := e₃ ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) (explicit₁₂ h₁) (explicit₁₂ nspk₂₂),
    have h₄ := @c₁right₂ σ  (@ΛNSPK σ i r n₁ n₂) (@ℂNSPK σ i n₁) r i n₁
      ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) 
      ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) 
      h₂,
    have h₅ := @e₁left₂ σ  (@ΛNSPK σ i r n₁ n₂) (@ℂNSPK σ i n₁) r i n₁
      ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) 
      ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) 
      h₃,
    exact explicit₂ h₄ h₅
  end 

  /-
    Man-in-the-Middle Attack in NSPK
  -/

  variables { e : agent σ }
  def MITM₁ : form σ := (X i, ι n₁)
  def MITM₂ : form σ := (X r, ι n₂) 
  def MITM₃ : form σ := ([send : i, e] ι (i.conc n₁).encr (e.pk))  
  def MITM₄ : form σ := (~([send : i, r] ι (i.conc n₁).encr (i.pk)))

  def ΛMITM : ctx σ := ((@MITM₁ σ i n₁) :: (@MITM₂ σ r n₂) :: (@MITM₃ σ i n₁ e) :: (@MITM₄ σ i r n₁) :: []) 
    ++ (@ΛNSPK σ i r n₁ n₂)

  theorem MITM_attack { σ : nat } { i r n₁ n₂ e : message σ }
    : (@ΛMITM σ i r n₁ n₂ e)-(@ℂNSPK σ i n₁) ⊢κ B r, ([send : i, r] ι ((i.conc n₁).encr (r.pk))) :=
    begin 
      have nsi₃ : (@ΛMITM σ i r n₁ n₂ e)-(@ℂNSPK σ i n₁) ⊢κ ([send : i, r] ι ((i.conc n₁).encr (r.pk))) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
      have h₁ := H₀ nsi₃,
      have hns₃ : (@ΛMITM σ i r n₁ n₂ e)-(@ℂNSPK σ i n₁) ⊢κ (([recv : r] ι (i.conc n₁).encr (r.pk)) ⊃ ((B r, [send : i, r] ι ((i.conc n₁).encr (r.pk))) & (B r, (X i, ι n₁)))) :=
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
      have h₂ := mp hns₃ h₁,
      exact andelim₁ h₂,
    end 

end NeedhamSchroeder


section BAN 
  /-
    BAN Logic 
  -/

  section BANAux 

    theorem explicit_implies_message { σ : nat } { Λ : ctx σ } { ℂ : constCtx σ }
      { i m : message σ }
      : Λ-ℂ ⊢κ (X i, ι m) ⊃ ι m := trans explicit₁₀ t  

  end BANAux 

  variables { i r m m₁ m₂ k kir : message σ }

  def MMSKBAN : form σ := (((X i, ι kir.keys i r) & ([recv : i] ι m.encr kir)) ⊃ (B i, [send : r, i] ι m))
  def MMPKBAN : form σ := (((X i, ι r.pk) & ([recv : i] ι m.encr (r.sk))) ⊃ (B i, [send : r, i] ι m))
  
  def BC₁ : form σ := (ι m₁ & ι m₂) ⊃ ι (m₁.conc m₂)
  def BC₂ : form σ := (ι kir.keys i r) ⊃ (ι kir.keys r i)
  def BC₃ : form σ := (ι (m.encr r.pk) & ι r.sk) ⊃ ι m 
  def BC₄ : form σ := (ι (m.encr r.sk) & ι r.pk) ⊃ ι m 
  def BC₅ : form σ := ((ι m) & (ι k)) ⊃ ι (m.encr k) 
  def BC₆ : form σ := ((ι m.encr (kir.keys i r)) & (ι k.keys i r)) ⊃ ι m
  def BH : agent σ -> form σ := λ a, (X a, ι m) ⊃ ([recv : a] (ι m))
  
  def ΛBAN : ctx σ := (@MMSKBAN σ i r m kir) :: (@MMPKBAN σ i r m) :: [] 

  theorem JR { σ : nat } { Λ : ctx σ } { ℂ : constCtx σ }
    { i j k : message σ }
    (h₁ : Λ-ℂ ⊢κ B i, B j, ι k)
    (h₂ : Λ-ℂ ⊢κ B i, ((B j, ι k) ⊃ (X j, ι k)))
    : Λ-ℂ ⊢κ B i, ι k := mp 
      (mp bk (bnec explicit_implies_message)) 
      (mp (mp bk h₂) h₁)  

  theorem NV { σ : nat } { Λ : ctx σ } { ℂ : constCtx σ }
    { i r n : message σ }
    : Λ-ℂ ⊢κ ((B i, ([send : r, i] ι n)) ⊃ (B i, (X r, ι n))) := mp bk (bnec H₁₀)

  theorem MMSK { σ : nat } { ℂ : constCtx σ }
    { i r m kir : message σ }
    (h₁ : (@ΛBAN σ i r m kir)-ℂ ⊢κ X i, ι kir.keys i r)
    (h₂ : (@ΛBAN σ i r m kir)-ℂ ⊢κ [recv : i] ι m.encr kir)
    : (@ΛBAN σ i r m kir)-ℂ ⊢κ B i, ([send : r, i] ι m) := 
    begin 
      have ban : (@ΛBAN σ i r m kir)-ℂ ⊢κ 
        (((X i, ι kir.keys i r) & ([recv : i] ι m.encr kir)) ⊃ (B i, [send : r, i] ι m)) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
      exact mp ban (andintro h₁ h₂)
    end 

  theorem MMPK { σ : nat } { ℂ : constCtx σ }
    { i r m kir : message σ }
    (h₁ : (@ΛBAN σ i r m kir)-ℂ ⊢κ (X i, ι r.pk))
    (h₂ : (@ΛBAN σ i r m kir)-ℂ ⊢κ ([recv : i] ι m.encr (r.sk)))
    : (@ΛBAN σ i r m kir)-ℂ ⊢κ B i, ([send : r, i] ι m) := 
    begin 
      have ban : (@ΛBAN σ i r m kir)-ℂ ⊢κ (((X i, ι r.pk) & ([recv : i] ι m.encr (r.sk))) ⊃ (B i, [send : r, i] ι m)) := 
        ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
      exact mp ban (andintro h₁ h₂)
    end 

    section ProtocolExample 
      -- S -> R: {I, pk(I)}sk(S)
      -- R -> I: {R, nR}sk(R)
      -- I -> R : {nR, I}sk(I)

      variables { I R S n : message σ }

      -- BAN Idealization 
      def P₁ : form σ := ([recv : R] ι (n.encr (S.sk)))
      def P₂ : form σ := ([recv : I] ι (n.encr (R.sk)))
      def P₃ : form σ := ([recv : R] ι (n.encr (I.sk)))

      -- BAN Assumptions 
      def A₁ : form σ := (X R, ι S.pk)
      def A₂ : form σ := (X I, ι R.pk)
      def A₃ : form σ := B R, (X S, ι I.pk) 
      def A₄ : form σ := B I, (X R, ι n)

      -- Logic defined by (P₁ - P₃) ∪ (A₁ - A₄) ∪ ΛBAN 

      def ΛBANP : ctx σ := (@P₁ σ I R S) :: (@P₂ σ I R n) :: (@P₃ σ I R n) 
        :: (@A₁ σ R S) :: (@A₂ σ I R) :: (@A₃ σ I R S) :: (@A₄ σ I R n) :: [] ++ (@ΛBAN σ I R n n) 

      -- We want to prove that I and R are mutual authenticated to each other through nR 
      -- in BAN: I believes that R believes that nR  

      theorem BAN_theory_subset_of_BANP_theory : (@ΛBAN σ I R n n) ⊆κ (@ΛBANP σ I R S n) := 
      begin 
        intro x, 
        intro ha, 
        cases ha, 
        {
          rw [ha],
          repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }
        },
        {
          cases ha, 
          {
            rw [ha],
            repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }
          },
          {
            cases ha,
          }
        }
      end

      theorem BAN_auth_from_I { σ : nat } { ℂ : constCtx σ } 
        { I R S n : message σ }
        : (@ΛBANP σ I R S n)-ℂ ⊢κ B I, (X R, ι n) := 
        begin 
          have p₂ : (@ΛBANP σ I R S n)-ℂ ⊢κ ([recv : I] ι (n.encr (R.sk))) := 
            ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
          have a₂ : (@ΛBANP σ I R S n)-ℂ ⊢κ (X I, ι R.pk) := 
            ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
          have mmpk : (@ΛBAN σ I R n n)-ℂ ⊢κ (((X I, ι R.pk) & ([recv : I] ι n.encr (R.sk))) ⊃ (B I, [send : R, I] ι n)) :=
            ax (by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem }),
          have h₀ : (@ΛBANP σ I R S n)-ℂ ⊢κ (((X I, ι R.pk) & ([recv : I] ι n.encr (R.sk))) ⊃ (B I, [send : R, I] ι n)) := 
            extension_is_consistent 
              ((by repeat { apply List.mem_cons_self <|> apply List.mem_cons_of_mem })) 
              (BAN_theory_subset_of_BANP_theory),
          have h₁ := mp h₀ (andintro a₂ p₂),
          exact mp NV h₁
        end  

    end ProtocolExample 


end BAN 