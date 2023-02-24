import init.data.set

section ImportFromSet
  theorem mem_insert_of_mem {α : Type*} {x : α} {s : set α} (y : α) : x ∈ s → x ∈ insert y s := or.inr
  theorem mem_insert {α : Type*} (x : α) (s : set α) : x ∈ insert x s := or.inl rfl
  theorem insert_subset_insert {α : Type* } { s t : set α } { a : α } (h : s ⊆ t) : insert a s ⊆ insert a t := λ x, or.imp_right (@h _)
end ImportFromSet

-- language -- 
inductive message (σ : ℕ) : Type 
  | null : fin σ -> message 

inductive program (σ : ℕ) : Type 
  | atomp : program -> program  
  | secv : program -> program -> program 
  | star : program -> program 

inductive form (σ : ℕ) : Type 
  | atom : fin σ -> form 
  | botm : form 
  | impl : form -> form -> form 
  | k : form -> form 
  | b : form -> form 
  | pdl : program σ -> form -> form 

section Notations 
  prefix `#` := form.atom 
  notation `⊥` := form.botm
  infix `⊃` := form.impl 
  notation `~`:40 p := form.impl p ⊥ 
  notation p `&` q := ~(p ⊃ (~q))
  notation p `or` q := ~((~p) & (~q))
  notation `K`:80 p := form.k p 
  notation `B`:80 p := form.b p 
  notation `[` α `]`:80 p := form.pdl α p 
  notation `[` α `][` β `]`:80 p := program.secv α β p 
  notation α `*`:80 := program.star α 
  --notation α `;` β := program.secv α β 
end Notations 

@[reducible]
def ctx (σ : nat) : Type := set (form σ)

@[reducible]
def constCtx (σ : nat) : Type := set (message σ)


/-
  Proof system 
-/

open form 
open message
open program 

section ProofSystem 
  inductive Proof { σ : ℕ } : ctx σ → constCtx σ → form σ → Prop 
  -- Propositional logic
  | ax { Λ } { ℂ : constCtx σ } { p : form σ } (h : p ∈ Λ) : Proof Λ ℂ p  
  | pl1 { Λ } { ℂ : constCtx σ } { p q : form σ } : Proof Λ ℂ (p ⊃ (q ⊃ p))
  | pl2 { Λ } { ℂ : constCtx σ } { p q r : form σ } : Proof Λ ℂ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
  | pl3 { Λ } { ℂ : constCtx σ } { p q } : Proof Λ ℂ (((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p))
  -- S5
  | kk { Λ } { ℂ : constCtx σ } { p q } : Proof Λ ℂ ((K (p ⊃ q)) ⊃ ((K p) ⊃ (K q)))
  | t { Λ } { ℂ : constCtx σ } { p } : Proof Λ ℂ ((K p) ⊃ p) 
  | s4 { Λ } { ℂ : constCtx σ } { p } : Proof Λ ℂ ((K p) ⊃ (K (K p))) 
  -- KD
  | bk { Λ } { ℂ : constCtx σ } { p q } : Proof Λ ℂ ((B (p ⊃ q)) ⊃ ((B p) ⊃ (B q)))
  | dox { Λ } { ℂ : constCtx σ } { p } : Proof Λ ℂ ((B p) ⊃ (~(B (~p))))
  | kb { Λ } { ℂ : constCtx σ }{ p } : Proof Λ ℂ ((K p) ⊃ (B p))
  -- PDL
  | pdlk { Λ } { ℂ : constCtx σ } { p q } (α : program σ) : Proof Λ ℂ (([α](p ⊃ q)) ⊃ (([α]p)  ⊃ ([α]q)))
  -- PDL*
  | pdlstar₁ { Λ } { ℂ : constCtx σ } { φ : form σ } { α : program σ } : Proof Λ ℂ ((φ & [α.secv α*]φ) ⊃ ([α*]φ))
  | pdlstar₂ { Λ } { ℂ : constCtx σ } { φ : form σ } { α : program σ } : Proof Λ ℂ ((φ & [α*](φ ⊃ [α]φ)) ⊃ ([α*]φ))
  -- Deductive rules 
  | mp { Λ } { ℂ : constCtx σ } { p q } (hpq: Proof Λ ℂ (p ⊃ q)) (hp : Proof Λ ℂ p) : Proof Λ ℂ q
  | knec { Λ } { ℂ : constCtx σ } { p } (h : Proof ∅ ℂ p) : Proof Λ ℂ (K p)
  | bnec { Λ } { ℂ : constCtx σ } { p } (h : Proof ∅ ℂ p) : Proof Λ ℂ (B p)
  | gen { Λ } { ℂ : constCtx σ } { p } (α : program σ) (h : Proof ∅ ℂ p) : Proof Λ ℂ ([α]p)

end ProofSystem

notation Λ `-` ℂ ` ⊢κ ` p := Proof Λ ℂ p
notation Λ `-` ℂ ` ⊬κ ` p := Proof Λ ℂ p -> false  

section SyntaxLemmas
  open Proof 

  variable { σ : nat }
  lemma idd { p : form σ } { ℂ : constCtx σ } { Γ : ctx σ } : 
    Γ-ℂ ⊢κ p ⊃ p := mp (mp (@pl2 σ Γ ℂ p (p ⊃ p) p) pl1) pl1

  theorem deduction { Γ : ctx σ } { ℂ : constCtx σ } { p q : form σ } :
    ((set.insert p Γ)-ℂ ⊢κ q) -> (Γ-ℂ ⊢κ p ⊃ q) :=
  begin 
    generalize eq : (set.insert p Γ) = Γ',
    intro h,
    induction h;
    subst eq, 
    { repeat { cases h_h },
      exact idd, 
      { 
        exact mp pl1 (ax h_h)
      }
    },
    { exact mp pl1 pl1 },
    { exact mp pl1 pl2 },
    { exact mp pl1 pl3 },
    { exact mp pl1 kk  },
    { exact mp pl1 t }, 
    { exact mp pl1 s4 },
    { exact mp pl1 bk },
    { exact mp pl1 dox },
    { exact mp pl1 kb },
    { exact mp 
      pl1
      (@pdlk σ Γ h_ℂ h_p h_q h_α)
    },
    { exact mp 
      pl1
      (@pdlstar₁ σ Γ h_ℂ h_φ h_α) 
    },
    { exact mp 
      pl1
      (@pdlstar₂ σ Γ h_ℂ h_φ h_α) },
    { apply mp,
      { exact (mp pl2 (h_ih_hpq rfl)) },
      { exact h_ih_hp rfl } 
    },
    { exact mp pl1 (knec h_h) },
    { exact mp pl1 (bnec h_h) },
    { exact mp 
      pl1
      (@gen σ Γ h_ℂ h_p h_α h_h) 
    }
  end 

  lemma sub_weak {Γ Δ : ctx σ} {ℂ : constCtx σ } {p : form σ} :
    (Δ-ℂ ⊢κ p) → (Δ ⊆ Γ) → (Γ-ℂ ⊢κ p) :=
    begin 
      intros h s, 
      induction h,
      { apply ax, exact s h_h },
      { exact pl1 },
      { exact pl2 },
      { exact pl3 },
      { exact kk },
      { exact t },
      { exact s4 },
      { exact bk },
      { exact dox },
      { exact kb },
      { exact @pdlk σ Γ h_ℂ h_p h_q h_α },
      { exact @pdlstar₁ σ Γ h_ℂ h_φ h_α },
      { exact @pdlstar₂ σ Γ h_ℂ h_φ h_α },
      { apply mp, 
        { exact h_ih_hpq s }, 
        { exact h_ih_hp s}
      },
      { exact knec h_h },
      { exact bnec h_h },
      { exact @gen σ Γ h_ℂ h_p h_α h_h}
    end 

    lemma weak { Γ : ctx σ } { ℂ : constCtx σ } { p q : form σ } : 
      (Γ-ℂ ⊢κ p) -> ((set.insert q Γ)-ℂ ⊢κ p) := 
    begin 
      intro h,
      induction h, 
      { apply ax, exact (mem_insert_of_mem _ h_h) }, 
      { exact pl1 },
      { exact pl2 },
      { exact pl3 },
      { exact kk },
      { exact t },
      { exact s4 },
      { exact bk },
      { exact dox },
      { exact kb },
      { exact pdlk h_α  },
      { exact pdlstar₁ },
      { exact pdlstar₂ },
      { apply mp, 
        { exact h_ih_hpq },
        { exact h_ih_hp }
      },
      { exact knec h_h },
      { exact bnec h_h },
      { exact gen h_α h_h}
    end 

    lemma subctx_ax {Γ Δ : ctx σ} {ℂ : constCtx σ} {p : form σ} :
      Δ ⊆ Γ → (Δ-ℂ ⊢κ p) → (Γ-ℂ ⊢κ p) :=
    begin
      intros s h,
      induction h,
      { apply ax (s h_h) },
      { exact pl1 },
      { exact pl2 },
      { exact pl3 },
      { exact kk },
      { exact t },
      { exact s4 },
      { exact bk },
      { exact dox },
      { exact kb },
      { exact pdlk h_α  },
      { exact pdlstar₁ },
      { exact pdlstar₂ },
      { apply mp, 
        { exact h_ih_hpq s },
        { exact h_ih_hp s }
      },
      { exact knec h_h },
      { exact bnec h_h },
      { exact gen h_α h_h}
    end

    lemma subctx_contr {Γ Δ : ctx σ} {ℂ : constCtx σ } {p : form σ}:
      Δ ⊆ Γ → ((Γ ∪ Δ)-ℂ ⊢κ p) → (Γ-ℂ ⊢κ p) :=
    begin
      generalize eq : Γ ∪ Δ = Γ',
      intros s h,
      induction h; subst eq,
      { cases h_h,
        { exact ax h_h },
        { exact ax (s h_h) } },
      { exact pl1 },
      { exact pl2 },
      { exact pl3 },
      { exact kk },
      { exact t },
      { exact s4 },
      { exact bk },
      { exact dox },
      { exact kb },
      { exact pdlk h_α  },
      { exact pdlstar₁ },
      { exact pdlstar₂ },
      { apply mp, 
        { exact h_ih_hpq rfl },
        { exact h_ih_hp rfl }
      },
      { exact knec h_h },
      { exact bnec h_h },
      { exact gen h_α h_h}
    end

    lemma cut { Γ : ctx σ } { ℂ : constCtx σ } {p q r : form σ} :
      (Γ-ℂ ⊢κ  p ⊃ q) -> (Γ-ℂ ⊢κ  q ⊃ r) -> (Γ-ℂ ⊢κ  p ⊃ r) :=
      λ hpq hqr, mp (mp pl2 (mp pl1 hqr)) hpq

    lemma pr {Γ : ctx σ} { ℂ : constCtx σ }  {p : form σ} :
      (set.insert p Γ)-ℂ ⊢κ p :=
    by apply ax; apply or.intro_left; simp

    lemma pr1 { Γ : ctx σ } { ℂ : constCtx σ }  {p q : form σ} :
      (set.insert q (set.insert p Γ))-ℂ ⊢κ p :=
    by apply ax; apply or.intro_right; apply or.intro_left; simp

    lemma pr2 { Γ : ctx σ } { ℂ : constCtx σ }{p q : form σ} :
      (set.insert q (set.insert p Γ))-ℂ ⊢κ q :=
    by apply ax; apply or.intro_left; simp

    lemma contrap { Γ : ctx σ } { ℂ : constCtx σ } {p q : form σ}:
      Γ-ℂ ⊢κ  ((~q) ⊃ (~p)) ⊃ (p ⊃ q) :=
      deduction (deduction (mp (mp pl3 pr1) (mp pl1 pr2) ))

    lemma dne { Γ : ctx σ } { ℂ : constCtx σ } { p : form σ } :
      Γ-ℂ ⊢κ (~~p) ⊃ p := 
      have h : Γ-ℂ ⊢κ (~~p) ⊃ ((~p) ⊃ (~p)) := mp pl1 idd, 
      mp (mp pl2 (cut pl1 pl3)) h

    lemma dni { Γ : ctx σ } { ℂ : constCtx σ } { p : form σ } :
      Γ-ℂ ⊢κ p ⊃ (~~p) :=
      mp contrap dne

    lemma not_impl {Γ : ctx σ} { ℂ : constCtx σ } {p q : form σ} : 
      Γ-ℂ ⊢κ (p ⊃ q) ⊃ ((~q) ⊃ (~p)) :=
    begin
      repeat { apply deduction },
      apply mp,
      { exact pr1 },
        apply mp,
        { apply ax,
          apply mem_insert_of_mem,
          apply mem_insert_of_mem,
          apply mem_insert },
        { exact pr2 }
    end

    lemma not_impl_to_and {p q : form σ} {Γ : ctx σ}  { ℂ : constCtx σ } :
      Γ-ℂ ⊢κ (~(p ⊃ q)) ⊃ (p & (~q)) :=
    begin
      repeat {apply deduction},
      apply (mp pr1),
      { apply deduction,
        apply mp,
        { apply dne },
        { exact (mp pr1 pr2) } },
    end

    lemma and_not_to_not_impl {p q : form σ} {Γ : ctx σ}  { ℂ : constCtx σ } :
      Γ-ℂ ⊢κ (p & (~q)) ⊃ ~(p ⊃ q) :=
    begin
      repeat {apply deduction},
      apply mp,
      { apply pr1 },
      { apply cut,
        { apply pr2 },
        { apply dni }
      }
    end

    lemma conv_deduction {Γ : ctx σ} { ℂ : constCtx σ } {p q : form σ} :
      (Γ-ℂ ⊢κ p ⊃ q) -> ((set.insert p Γ)-ℂ ⊢κ q) := λ h, mp (weak h) pr 

    lemma ex_falso {Γ : ctx σ} {p : form σ} { ℂ : constCtx σ } :
      (Γ-ℂ ⊢κ  ⊥) → (Γ-ℂ ⊢κ p) :=
    begin
      intro h,
      apply mp,
      { exact dne },
      { apply mp,
        { exact pl1 },
        { exact h } }
    end

end SyntaxLemmas

@[reducible]
def world (σ : nat) := ctx σ 

variable { σ : nat }

structure Model := 
  (worlds : set (world σ))
  (Rk : world σ -> world σ -> bool)
  (Rb : world σ -> world σ -> bool)
  (Rp : world σ -> world σ -> bool)
  (val : fin σ -> world σ -> bool)
  (pdlval : program σ -> set ((world σ) × (world σ)))
  (krefl : ∀ w ∈ worlds, Rk w w = tt)
  (ksymm : ∀ w ∈ worlds, ∀ v ∈ worlds, Rk w v = tt -> Rk v w = tt)
  (ktrans : ∀ w ∈ worlds, ∀ v ∈ worlds, ∀ u ∈ worlds, Rk w v = tt -> Rk v u = tt -> Rk w u = tt)
  (bserial : ∀ w ∈ worlds, ∃ v ∈ worlds, Rb w v = tt)
  (ksubsetb : ∀ w ∈ worlds, ∀ v ∈ worlds, Rk w v = tt -> Rb w v = tt)

open classical 

local attribute [instance] prop_decidable

def big_union {α : Type*} {β : Type*} (s : set α) (f : α → set β) : set β := { b | ∃ a ∈ s, b ∈ f a }

def kleene_star {β : Type*} (a : set β) : ℕ → set β
| 0 := ∅
| (n+1) := a ∪ big_union (kleene_star n) (λ s, set.insert s a)


def compose { X Y Z : Type* } (R : set (X × Y)) (S : set (Y × Z)) : set (X × Z) :=
  set_of (λ ac, ∃ b, (ac.1, b) ∈ R ∧ (b, ac.2) ∈ S)

def mK {σ : nat} (M : @Model σ) : program σ -> set ((world σ) × (world σ))
| (@atomp σ a) := M.pdlval a 
| (@secv σ α β) := compose (M.pdlval α) (M.pdlval β)
| (@star σ α) := kleene_star (M.pdlval α) 3

open program 

noncomputable def forces_form (M : @Model σ) : form σ -> world σ -> bool
  | (@atom σ p)  := λ w, M.val p w 
  | (@botm σ) := λ w, ff 
  | (@impl σ p q) := λ w, bnot (forces_form p w) || (forces_form q w)
  | (@k σ p) := λ w, 
      if (∀ v ∈ M.worlds, w ∈ M.worlds -> M.Rk w v = tt -> forces_form p v = tt) 
        then tt 
      else ff
  | (@b σ p) := λ w, 
      if (∀ v ∈ M.worlds, w ∈ M.worlds -> M.Rb w v = tt -> forces_form p v = tt) 
        then tt 
      else ff
  | (@pdl σ α p) := λ w, 
      if (∀ v ∈ M.worlds, w ∈ M.worlds -> ((v,w) ∈ (@mK σ M α)) -> forces_form p v = tt)
        then tt 
      else ff

notation w `⊩` `⦃` M `⦄` p := forces_form M p w 

noncomputable def forces_ctx (M : @Model σ) (Γ : ctx σ) : world σ -> bool := 
  λ w, if (∀ p, p ∈ Γ -> forces_form M p w = tt) then tt else ff 

notation w `⊩` `⦃` M `⦄ ` p := forces_ctx M p w

inductive sem_csq (Γ : ctx σ) (ℂ : constCtx σ) (p : form σ) : Prop 
  | is_true (m : ∀ (M : @Model σ) (w ∈ M.worlds), ((w ⊩⦃M⦄ Γ) = tt) → (w ⊩⦃M⦄ p) = tt) : sem_csq

notation Λ `-` ℂ ` ⊧κ ` p := sem_csq Λ ℂ p 


lemma neg_tt_iff_ff { M : @Model σ } { w : world σ } { p : form σ } :
  (w ⊩ ⦃M⦄ ~p) = tt ↔ ¬(w ⊩ ⦃M⦄ p) := 
  begin 
    unfold forces_form, 
    have h := forces_form M p w,
    induction h, 
    simp, 
    simp 
  end 

lemma neg_ff_iff_tt { M : @Model σ }  {w : world σ} {p : form σ} :
  ¬(w ⊩⦃M⦄ ~p) ↔ (w ⊩⦃M⦄ p) = tt :=
  begin 
    unfold forces_form,
    induction (forces_form M p w),
    simp,
    simp
  end 

lemma impl_iff_implies { M : @Model σ }  {w : world σ} {p q : form σ} :
  (w ⊩⦃M⦄ (p ⊃ q)) = tt ↔ ((w ⊩⦃M⦄ p) → (w ⊩⦃M⦄ q)) := 
  begin 
    unfold forces_form, 
    have h := forces_form M p w, 
    induction h, 
    repeat { 
      have h₁ := forces_form M q w, 
      induction h₁, 
      simp
    }
  end 

@[simp] 
lemma impl_tt_iff_ff_or_tt {M : @Model σ} {w : world σ} {p q : form σ} :
  (w ⊩⦃M⦄ p ⊃ q) = tt ↔ ¬(w ⊩⦃M⦄ p) ∨ (w ⊩⦃M⦄ q) = tt :=
  begin
    unfold forces_form, 
    have h := forces_form M p w, 
    induction h, 
    { have h₁ := forces_form M q w, 
      induction h₁, 
      { simp  },
      { simp }  
    },
    { have h₁ := forces_form M q w, 
      induction h₁, 
      { simp  },
      { simp } 
    }
  end 

lemma ff_or_tt_and_tt_implies_tt_right {M : @Model σ} {w : world σ} {p q : form σ} :
  (¬(w ⊩⦃M⦄ p) ∨ (w ⊩⦃M⦄ q) = tt) → (w ⊩⦃M⦄ p) = tt → (w ⊩⦃M⦄ q) = tt :=
  begin
    unfold forces_form,
    have h := forces_form M p w,
    induction h,
    {
      have h₁ := forces_form M q w, 
      induction h₁, 
      { simp }, 
      { simp }
    },
    {
      have h₂ := forces_form M q w,
      induction h₂,
      { simp },
      { simp }
    }
  end 
-- by simp; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma bot_is_insatisf (w : world σ) : 
  ¬ ∃ (M : @Model σ), (w ⊩ ⦃M⦄ (@botm σ)) = tt := 
  begin 
    intro h,
    cases h,
    exact (bool.no_confusion h_h) 
  end 

lemma forall_wrld_tt_nec_tt { M : @Model σ } {w : world σ} {p : form σ} : 
  (∀ v ∈ M.worlds, w ∈ M.worlds -> M.Rk w v -> (v ⊩ ⦃M⦄ p) = tt) -> (w ⊩⦃M⦄ K p) = tt := 
  begin 
    intro h, 
    unfold forces_form,
    induction (prop_decidable _),
    { simp, contradiction },
    { simp, assumption }
  end 

lemma is_true_pl1 { M : @Model σ } { w : world σ } { p q : form σ } : 
  (w ⊩ ⦃M⦄ (p ⊃ (q ⊃ p))) = tt := 
  begin 
    apply impl_iff_implies.2,
    intro h,
    unfold forces_form, 
    simp [*],
  end 

lemma is_true_pl2 { M : @Model σ } { w : world σ } { p q r : form σ } :
  (w ⊩⦃M⦄ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))) = tt := 
  begin 
    apply impl_iff_implies.2,
    intro h₁, apply impl_iff_implies.2,
    intro h₂, apply impl_iff_implies.2,
    intro h₃, apply impl_iff_implies.1 ((impl_iff_implies.1 h₁) h₃),
    apply impl_iff_implies.1 h₂, assumption
  end 

lemma is_true_pl3 { M : @Model σ } { w : world σ } { p q : form σ } : 
  (w ⊩⦃M⦄ ((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p)) = tt := 
  begin 
    unfold forces_form,
    induction (forces_form M p w),
    repeat { induction (forces_form M q w), repeat {simp} },
  end 

lemma nec_impl_to_nec_to_nec {M : @Model σ} {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ (K(p ⊃ q))) = tt → (w ⊩⦃M⦄ (K p)) = tt → (w ⊩⦃M⦄ (K q)) = tt := 
begin
  unfold forces_form, 
  simp at *,
  intros hlpq hlp v wmem vmem rwv, 
  specialize hlpq v, 
  specialize hlp v, 
  have h₁ := ((hlpq wmem) vmem) rwv,
  have h₂ := (((hlp) wmem) vmem) rwv,
  simp [*] at *
end 

lemma bnec_impl_to_bnec_to_bnec {M : @Model σ} {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ (B(p ⊃ q))) = tt → (w ⊩⦃M⦄ (B p)) = tt → (w ⊩⦃M⦄ (B q)) = tt := 
begin
  unfold forces_form, 
  simp at *,
  intros hlpq hlp v wmem vmem rwv, 
  specialize hlpq v, 
  specialize hlp v, 
  have h₁ := ((hlpq wmem) vmem) rwv,
  have h₂ := (((hlp) wmem) vmem) rwv,
  simp [*] at *
end 

lemma pdlnec_impl_to_pdlnec_to_pdlnec {M : @Model σ} {w : world σ} {p q : form σ} {α : program σ} : 
  (w ⊩⦃M⦄ ([α](p ⊃ q))) = tt → (w ⊩⦃M⦄ ([α] p)) = tt → (w ⊩⦃M⦄ ([α] q)) = tt := 
begin
  unfold forces_form, 
  simp at *,
  intros hlpq hlp v wmem vmem rwv, 
  specialize hlpq v, 
  specialize hlp v, 
  have h₁ := ((hlpq wmem) vmem) rwv,
  have h₂ := (((hlp) wmem) vmem) rwv,
  simp [*] at *
end 

lemma nec_nec_to_nec_impl {M : @Model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ (K p)) = tt → (w ⊩⦃M⦄ (K q)) = tt → (w ⊩⦃M⦄ K (p ⊃ q)) = tt  := 
begin 
  unfold forces_form, 
  simp at *,
  intros hp hq v wmem vmem rwv,
  specialize hp v, 
  specialize hq v,
  have h₁ := ((hp wmem) vmem) rwv,
  have h₂ := ((hq wmem) vmem) rwv,
  simp [*] 
end 

@[simp]
lemma nec_impl_to_nec_impl_nec {M : @Model σ} {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ K (p ⊃ q)) = tt → (¬(w ⊩⦃M⦄ K p) ∨ (w ⊩⦃M⦄ K q) = tt) := 
begin 
  intro h₀, 
  cases prop_decidable ((w ⊩⦃M⦄ K p) = tt),
  simp at h, left,
  simp at *, assumption, 
  right, apply nec_impl_to_nec_to_nec h₀ h 
end 

@[simp]
lemma bnec_impl_to_bnec_impl_bnec {M : @Model σ} {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ B (p ⊃ q)) = tt → (¬(w ⊩⦃M⦄ B p) ∨ (w ⊩⦃M⦄ B q) = tt) := 
begin 
  intro h₀, 
  cases prop_decidable ((w ⊩⦃M⦄ B p) = tt),
  simp at h, left,
  simp at *, assumption, 
  right, apply bnec_impl_to_bnec_to_bnec h₀ h 
end

@[simp]
lemma pdlnec_impl_to_pdlnec_impl_pdlnec {M : @Model σ} {w : world σ} {p q : form σ} {α : program σ} : 
  (w ⊩⦃M⦄ ([α] (p ⊃ q))) = tt → (¬(w ⊩⦃M⦄ ([α] p)) ∨ (w ⊩⦃M⦄ ([α] q)) = tt) := 
begin 
  intro h₀, 
  cases prop_decidable ((w ⊩⦃M⦄ ([α] p)) = tt),
  simp at h, left,
  simp at *, assumption, 
  right, apply pdlnec_impl_to_pdlnec_to_pdlnec h₀ h 
end


lemma is_true_k { M : @Model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ ((K(p ⊃ q)) ⊃ ((K p) ⊃ K q))) = tt := 
    impl_iff_implies.2 (λ h, impl_tt_iff_ff_or_tt.2 (nec_impl_to_nec_impl_nec h))

lemma is_true_bk { M : @Model σ } { w : world σ } { p q : form σ } : 
  (w ⊩⦃M⦄ ((B(p ⊃ q)) ⊃ ((B p) ⊃ B q))) = tt := 
    impl_iff_implies.2 (λ h, impl_tt_iff_ff_or_tt.2 (bnec_impl_to_bnec_impl_bnec h))

lemma is_true_pdlk { M : @Model σ } { w : world σ } { p q : form σ } { α : program σ } :
  (w ⊩⦃M⦄ (([α](p ⊃ q)) ⊃ (([α] p) ⊃ ([α] q)))) = tt := 
    impl_iff_implies.2 (λ h, impl_tt_iff_ff_or_tt.2 (pdlnec_impl_to_pdlnec_impl_pdlnec h))

lemma nec_to_tt {M : @Model σ } {w : world σ} {wm : w ∈ M.worlds} {p : form σ} :
  (w ⊩⦃M⦄ K p) = tt → (w ⊩⦃M⦄ p) = tt := 
begin
  unfold forces_form, simp at *,
  intro f, apply f, repeat {assumption},
  apply M.krefl, assumption
end

lemma is_true_t {M : @Model σ } {w : world σ} {w ∈ M.worlds} {p : form σ} : 
  (w ⊩⦃M⦄ (K p) ⊃ p) = tt := 
by apply impl_iff_implies.2; apply nec_to_tt; repeat {assumption}

lemma np_or_q_is_p_imp_q { p q : Prop } : (¬p ∨ q) ↔ (p → q) :=
begin
  split,
  {
    intros h₁ h₂,
    cases h₁ with hnp hq,
    { exfalso, apply hnp, exact h₂,},
    { exact hq, }
  },
  {
    intros h₁,
    by_cases hp : p,
    { right, exact h₁ hp, },
    { left, exact hp, }
  }
end


lemma is_true_dox { M : @Model σ } { w : world σ } {w ∈ M.worlds} {p : form σ } :
  (w ⊩ ⦃M⦄ ((B p) ⊃ ~B(~p))) = tt := 
  begin 
    unfold forces_form,
    simp,
    rw [np_or_q_is_p_imp_q],
    intros h_h,
    have serial := M.bserial,
    specialize serial w,
    have h₂ := (serial H),
    cases h₂ with h₂e h₂b, 
    cases h₂b with h₂be h₂bb, 
    specialize h_h h₂e, 
    have h₁ := ((h_h h₂be) H) h₂bb,
    clear h_h,
    intro h_c,
    specialize h_c h₂e, 
    have h₂ := ((h_c h₂be) H) h₂bb,
    clear h_c h₂be h₂bb, 
    simp [*] at *,
  end 

lemma pl2_nd { p q r : Prop } : (p → q) → (p → r) → (p → (q → r)) := 
  λ h₁ : p → q,
  λ h₂ : p → r,
  λ h₃ : p,
  λ h₄ : q,
  show r, from h₂ h₃ 


lemma is_true_kb { M : @Model σ } { w : world σ } { w ∈ M.worlds } { p : form σ } :
  (w ⊩ ⦃M⦄ ((K p) ⊃ (B p))) = tt :=
  begin 
    unfold forces_form,
    simp,
    rw [np_or_q_is_p_imp_q],
    intros h_h,
    have subset := Model.ksubsetb,
    specialize subset M w,
    intros v vmem wmem wRbv,
    have h₁ := subset H,
    clear subset,
    specialize h₁ v,
    specialize h_h v,
    have h₂ := h₁ vmem,
    have h₃ := (h_h vmem) wmem,
    clear h₁ h_h,
    have h₄ := pl2_nd h₂ h₃,  
  end  

lemma is_true_pdlstar₁ { M : @Model σ } { w : world σ } { w ∈ M.worlds } { p : form σ } { α : program σ } :
  (w ⊩ ⦃M⦄ (((p & [α.secv α*]p) ⊃ ([α*]p)))) = tt := 
  begin 
    unfold forces_form,
    simp [*],  
  end 

lemma is_true_pdlstar₂{ M : @Model σ } { w : world σ } { w ∈ M.worlds } { p : form σ } { α : program σ } :
  (w ⊩ ⦃M⦄ (((p & [α*](p ⊃ [α]p)) ⊃ ([α*]p)))) = tt := 
  begin 
    unfold forces_form,
    simp [*],  
  end 


lemma nec_to_nec_of_nec {M : @Model σ } {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ K p) = tt → (w ⊩⦃M⦄ K (K p)) = tt := 
begin
  unfold forces_form, simp at *,
  intros f v wmem vmem rwv u vmem' umem rvu,
  apply f, repeat {assumption},
  refine M.ktrans _ _ _ _ _ _ rwv rvu,
  repeat {assumption}
end

lemma is_true_s4 { M : @Model σ } {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ ((K p) ⊃ (K (K p)))) = tt := 
by apply impl_iff_implies.2; apply nec_to_nec_of_nec

lemma ctx_tt_iff_mem_tt {Γ : ctx σ} {M : @Model σ} {w : world σ} :
  (w ⊩⦃M⦄ Γ) = tt ↔ (∀ p, p ∈ Γ → (w ⊩⦃M⦄ p) = tt) :=
begin
  unfold forces_ctx,
  induction (classical.prop_decidable _),
  { apply iff.intro,
    simp, intro h₁,
    intro φ,
    specialize h₁ φ,
    { exact h₁ },
    { contradiction }
  },
  { simp }
end

lemma mem_tt_to_ctx_tt (Γ : ctx σ) {M : @Model σ } {w : world σ} :
  (∀ (p : form σ) (h : p ∈ Γ), (w ⊩⦃M⦄ p) = tt) → (w ⊩⦃M⦄ Γ) = tt :=
ctx_tt_iff_mem_tt.2

lemma ctx_tt_to_mem_tt {Γ : ctx σ} {M : @Model σ} {w : world σ} {p : form σ} :
  (w ⊩⦃M⦄ Γ) = tt → p ∈ Γ → (w ⊩⦃M⦄ p) = tt :=
by intro; apply ctx_tt_iff_mem_tt.1; assumption

lemma empty_ctx_tt {M : @Model σ} {w : world σ} : 
  (w ⊩⦃M⦄ ∅) = tt :=
begin
  apply ctx_tt_iff_mem_tt.2,
  intros, exfalso, assumption
end



lemma cons_ctx_tt_iff_and {Γ : ctx σ} {M : @Model σ } {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ (set.insert p Γ)) = tt ↔ (w ⊩⦃M⦄ Γ) = tt ∧ (w ⊩⦃M⦄ p) = tt :=
begin
  unfold forces_ctx,
  induction (classical.prop_decidable (∀ p, p ∈ Γ → forces_form M p w = tt)),
  { simp, apply iff.intro,
    { intro h', exfalso, 
      apply h, intros q qmem, apply h',
      apply mem_insert_of_mem, assumption },
    { intros h' q qmem,
      cases h', cases qmem,
      rw qmem, assumption,
      apply h'_left, assumption } },

  { simp, apply iff.intro,
    { intro h', split,
      { assumption },
      { apply h', apply mem_insert } },
    { intros h' q qmem,
      cases h', cases qmem,
      rw qmem, assumption,
      apply h'_left, assumption } },
end

lemma cons_ctx_tt_to_ctx_tt {Γ : ctx σ} {M : @Model σ } {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ (set.insert p Γ)) = tt → (w ⊩ ⦃M⦄ Γ) = tt :=
by intro h; apply and.elim_left; apply cons_ctx_tt_iff_and.1 h

lemma ctx_tt_cons_tt_to_cons_ctx_tt {Γ : ctx σ} {M : @Model σ } {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ Γ) = tt → (w ⊩⦃M⦄ p) → (w ⊩⦃M⦄ (set.insert p Γ)) :=
by intros hg hp; apply cons_ctx_tt_iff_and.2; split; assumption; assumption

lemma ctx_tt_to_subctx_tt {Γ Δ : ctx σ} {M : @Model σ } {w : world σ} : 
  (w ⊩⦃M⦄ Γ) → Δ ⊆ Γ → (w ⊩⦃M⦄ Δ) :=
begin
  intros h s, 
  apply ctx_tt_iff_mem_tt.2, 
  intros p pmem,
  apply ctx_tt_iff_mem_tt.1 h,
  apply s, exact pmem
end

lemma sem_deduction {Γ : ctx σ} { ℂ : constCtx σ } {p q : form σ} :
  ((set.insert p Γ)-ℂ ⊧κ  q) → (Γ-ℂ ⊧κ p ⊃ q) :=
begin
  intro h, cases h,
  apply sem_csq.is_true,
  intros M w wmem ant,
  apply impl_iff_implies.2,
  { intro hp, apply h, assumption,
    apply ctx_tt_cons_tt_to_cons_ctx_tt, 
    repeat {assumption} }
end

theorem soundness { Γ : ctx σ } { ℂ : constCtx σ } { p : form σ } :
  (Γ-ℂ ⊢κ p) -> (Γ-ℂ ⊧κ p) := 
begin 
  intro h,
  induction h,
  {
    apply sem_csq.is_true,
    intros,
    apply ctx_tt_to_mem_tt,
    repeat {assumption}
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_pl1
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_pl2
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_pl3
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_k
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_t,
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_s4
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_bk
  }, 
  { 
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_dox,
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_kb,
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pdlk
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pdlstar₁,
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pdlstar₂, 
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    induction h_ih_hpq,
    induction h_ih_hp,
    intros M w wmem ctt,
    revert h_ih_hpq,
    unfold forces_form, simp,
    intro hpq,
    cases (hpq M w wmem ctt),
    { simp [*] at * },
    { 
      exact h
    } 
  },
  {
    apply sem_csq.is_true, 
    intros M w wmem ctt, 
    unfold forces_form,
    simp, 
    induction h_ih, 
    intros v vmem wmem rwv, 
    apply h_ih, assumption,
    apply empty_ctx_tt
  },
  {
    apply sem_csq.is_true, 
    intros M w wmem ctt, 
    unfold forces_form,
    simp, 
    induction h_ih, 
    intros v vmem wmem rwv, 
    apply h_ih, assumption,
    apply empty_ctx_tt 
  },
  {
    apply sem_csq.is_true, 
    intros M w wmem ctt, 
    unfold forces_form,
    simp, 
    induction h_ih, 
    intros v vmem wmem rwv, 
    apply h_ih, assumption,
    apply empty_ctx_tt
  }
end 

local attribute [priority 0] prop_decidable 

open Proof 

def is_consist { ℂ : constCtx σ } (Γ : ctx σ) := (Γ-ℂ ⊬κ ⊥)


lemma consist_not_of_not_prf { ℂ : constCtx σ } { Γ : ctx σ } { p : form σ } { α : program σ }:
  (Γ-ℂ ⊬κ p) -> @is_consist σ ℂ (set.insert (~p) Γ) := 
  λ hnp hc, hnp (mp dne 
  (deduction hc))

lemma not_prf_of_consist_not {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
  @is_consist σ ℂ (set.insert (~p) Γ) → (Γ-ℂ ⊬κ p) :=
  λ h c, h (conv_deduction (mp dni c))

lemma consist_of_not_prf {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} : 
  (Γ-ℂ ⊢κ p) → @is_consist σ ℂ Γ := λ nhp nc, nhp (ex_falso nc)

lemma inconsist_to_neg_consist {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
  @is_consist σ ℂ Γ → ¬@is_consist σ ℂ (set.insert p Γ) → @is_consist σ ℂ (set.insert (~p) Γ) :=
begin
  intros c nc hp, apply c, apply mp,
    apply deduction, apply by_contradiction nc,
    apply mp dne, exact (deduction hp),
end

lemma inconsist_of_neg_to_consist {Γ : ctx σ} { ℂ : constCtx σ }  {p : form σ} :
  @is_consist σ ℂ Γ → ¬@is_consist σ ℂ (set.insert (~p) Γ) → @is_consist σ ℂ (set.insert p Γ) :=
begin
  intros c nc hp, apply c, apply mp,
  { apply deduction (by_contradiction nc) },
  { exact deduction hp },
end

lemma consist_fst {Γ : ctx σ} { ℂ : constCtx σ }  {p : form σ} :
  @is_consist σ ℂ (set.insert p Γ) → @is_consist σ ℂ Γ :=
λ hc hn, hc (weak hn)

lemma consist_ext {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
  @is_consist σ ℂ Γ → (Γ-ℂ ⊬κ ~p) → @is_consist σ ℂ (set.insert p Γ) :=
by intros c np hn; apply np (deduction hn)

lemma inconsist_ext_to_inconsist {Γ : ctx σ} { ℂ : constCtx σ }  {p : form σ} :
    ((¬ @is_consist σ ℂ (set.insert p Γ)) ∧ ¬ @is_consist σ ℂ(set.insert (~p) Γ)) → ¬ @is_consist σ ℂ (Γ) :=
begin
  intros h nc, cases h,
  have h₁ : ((set.insert p Γ)-ℂ ⊢κ ⊥) := by_contradiction h_left,
  have h₂ : ((set.insert (~p) Γ)-ℂ ⊢κ ⊥) := by_contradiction h_right,
  apply nc, apply mp (deduction h₁),
    apply mp dne (deduction h₂)
end

lemma consist_to_consist_ext {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
    @is_consist σ ℂ (Γ) → (@is_consist σ ℂ (set.insert p Γ) ∨ @is_consist σ ℂ (set.insert (~p) Γ)) :=
begin
  intro c, apply classical.by_contradiction, intro h, 
  apply absurd c, apply inconsist_ext_to_inconsist,
  apply (decidable.not_or_iff_and_not _ _).1, apply h,
  repeat {apply (prop_decidable _)}
end

lemma pos_consist_mem {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
  p ∈ Γ → @is_consist σ ℂ (Γ) → (~p) ∉ Γ :=
λ hp hc hnp, hc (mp (ax hnp) (ax hp))

lemma neg_consist_mem {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
  (~p) ∈ Γ → @is_consist σ ℂ (Γ) → p ∉ Γ :=
λ hnp hc hp, hc (mp (ax hnp) (ax hp))

lemma pos_inconsist_ext {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} (c : @is_consist σ ℂ Γ) :
  p ∈ Γ → ¬ @is_consist σ ℂ (set.insert p Γ) → (~p) ∈ Γ :=
begin
  intros hp hn,
  exfalso, apply c,
  apply mp, apply deduction (by_contradiction hn),
  apply ax hp
end

lemma neg_inconsist_ext {Γ : ctx σ} { ℂ : constCtx σ } {p : form σ} (c : @is_consist σ ℂ Γ) :
  (~p) ∈ Γ → ¬ @is_consist σ ℂ (set.insert (~p) Γ) → p ∈ Γ :=
begin
  intros hp hn,
  exfalso, apply c,
  apply mp, apply deduction (by_contradiction hn),
  apply ax hp
end

/- context extensions of subcontexts -/

lemma sub_preserves_consist {Γ Δ : ctx σ} { ℂ : constCtx σ } :
  @is_consist σ ℂ Γ → @is_consist σ ℂ Δ → Δ ⊆ Γ → @is_consist σ ℂ (Γ ∪ Δ) :=
by intros c1 c2 s nc; apply c1; exact (subctx_contr s nc)

lemma subctx_inherits_consist {Γ Δ : ctx σ} { ℂ : constCtx σ } {p : form σ} :
  @is_consist σ ℂ Γ → @is_consist σ ℂ Δ → Γ ⊆ Δ → @is_consist σ ℂ (set.insert p Δ) → @is_consist σ ℂ (set.insert p Γ) :=
by intros c1 c2 s c nc; apply c; apply conv_deduction; apply subctx_ax s (deduction nc)



lemma inconsist_sub {Γ Δ : ctx σ} {p : form σ} { ℂ : constCtx σ } (c : @is_consist σ ℂ Γ) :
  ¬ @is_consist σ ℂ (set.insert p Δ) → Δ ⊆ Γ → ¬ @is_consist σ ℂ (set.insert p Γ) :=
begin
  unfold is_consist, intros h s c, apply c,
  apply subctx_ax, apply insert_subset_insert s,
  apply classical.by_contradiction h
end


lemma tt_to_const {Γ : ctx σ} { ℂ : constCtx σ } {M : @Model σ } {w ∈ M.worlds} :
  (w ⊩⦃M⦄ Γ) = tt → @is_consist σ ℂ Γ :=
begin
  intros h hin,
  cases (soundness hin),
  apply bot_is_insatisf,
  apply exists.intro,
  refine (m M w _ h),
  repeat {assumption},
end

