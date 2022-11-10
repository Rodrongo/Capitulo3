--=============================--
------ LÓGICA PROPOSICIONAL------
--=============================--

-- En lógica clásica, la doble negación de p y p son equivalentes
theorem iff_not_not {p : Prop} : ¬¬p ↔ p := 
  Iff.intro
  Classical.byContradiction
  (fun hp : p => fun hnp : ¬p => (hnp hp))


theorem notfalse_iff_true : ¬False ↔ True :=
  ⟨fun _ => True.intro, fun _ hfalse => hfalse⟩

theorem nottrue_iff_false : ¬True ↔ False :=
  ⟨fun hnottrue => hnottrue True.intro, fun hfalse => hfalse.elim⟩  

theorem forall_of_not_exists {p : α → Prop} : ¬ (∃ a, p a) → ∀ a, ¬ p a :=
  fun h a hpa => h ⟨a,hpa⟩

-- El contrarrecíproco de una implicación
theorem contrapositive {p q : Prop} : (p → q) → ¬q → ¬p :=
  fun hpq hnq hp => hnq (hpq hp)

theorem implies_of_not_and {p q : Prop} : ¬ (p ∧ q) → (p → ¬ q) :=
  fun hnpq hp hq => hnpq ⟨hp,hq⟩

theorem or_not_iff_not_and {p q : Prop} : ¬ (p ∧ q) ↔ ¬p ∨ ¬q := 
  ⟨fun hnpq : ¬(p ∧ q) =>
    Or.elim (Classical.em p)
    (fun hp => Or.inr (fun hq => hnpq ⟨hp,hq⟩))
    (fun hnp => Or.inl hnp),
  fun hnpnq : ¬p ∨ ¬q =>
    fun ⟨hp,hq⟩ => hnpnq.elim (fun hnp => hnp hp) (fun hnq => hnq hq)⟩

-- Una de las leyes de De Morgan
theorem and_or_iff {p q1 q2: Prop} : p ∧ (q1 ∨ q2) ↔ (p ∧ q1) ∨ (p ∧ q2) :=
  ⟨fun h => h.right.elim (fun hq1 => Or.inl ⟨h.left,hq1⟩) (fun hq2 => Or.inr ⟨h.left,hq2⟩),
  fun h => h.elim (fun hpq1 => ⟨hpq1.left, Or.inl hpq1.right⟩) (fun hpq2 => ⟨hpq2.left, Or.inr hpq2.right⟩)⟩

-- El recíproco del principio de extensionalidad funcional
theorem funext_converse {f g : α → β} : f ≠ g → ∃ x : α, f x ≠ g x :=
  fun hneq =>
    Classical.byContradiction (fun hnotex => 
      have hforall1 : ∀ x, ¬ f x ≠ g x := forall_of_not_exists hnotex
      have hforall : ∀ x, f x = g x := fun x => propext (@iff_not_not (f x = g x)) ▸ (hforall1 x)
      hneq (funext hforall))