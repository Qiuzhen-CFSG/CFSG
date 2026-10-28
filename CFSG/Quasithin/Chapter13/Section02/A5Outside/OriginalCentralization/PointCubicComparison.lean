module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointDegreeThree
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.TripleRows.Orders
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# Cubic central-cover comparisons in the original point action

The point comparison has a solvable kernel, while the F.6.18(6)--(9) source
rows carry a central cubic cover. The kernel therefore has only two possible
positions: it is trivial, or it is the full cubic center. In the latter case
the original map descends to the literal alternating or symmetric quotient,
with the original quotient map retained. The covered seven-point rows are
then separated from the B.5 component catalogue by their actual order.

This module keeps the central cover intact and does not identify an ambient
group from a family label or from order alone. It is consumed by the source
assembly when the corresponding F.6 rows are selected.
Source: Aschbacher--Smith F.6.18(6)--(9), printed pp.309--310, and
13.2.12, printed p.882.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

private theorem prime_subgroup_dichotomy {A : Type*} [Group A] [Finite A]
    {K Z : Subgroup A} (hk : K ≤ Z) (hz : Nat.card Z = 3) : K = ⊥ ∨ K = Z := by
  have hd : Nat.card K ∣ 3 := hz ▸ card_dvd_of_le hk
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hc | hc
  · exact Or.inl (K.eq_bot_iff_card.mpr hc)
  · exact Or.inr (eq_of_le_of_card_ge hk (by omega))

private theorem quotient_equiv_of_kernel {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (hf : Function.Surjective f) (Z : Subgroup A) [Z.Normal]
    (hk : f.ker = Z) (e : (A ⧸ Z) ≃* C) :
    ∃ a : B ≃* C, ∀ x : A, a (f x) = e (QuotientGroup.mk' Z x) := by
  let a := ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)).trans e
  refine ⟨a,?_⟩
  intro x
  change e (QuotientGroup.quotientMulEquivOfEq hk
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x))) = _
  have hx : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) =
      QuotientGroup.mk' f.ker x := by
    apply (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hx]
  rfl

private theorem cubic_card {A : Type*} [Group A] {n : ℕ}
    (h : FSource.TripleAlternating A n) : Nat.card (center A) = 3 := by
  rw [Nat.card_congr h.center.some.toEquiv]
  simp [FSource.C]

private theorem cubic_quasisimple {A : Type*} [Group A] {n : ℕ}
    (h : FSource.TripleAlternating A n) (hn : 5 ≤ n) : IsQuasisimple A := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  exact { toIsPerfect := h.perfect, simple := h.quotient.some.isSimpleGroup }

private theorem fitting_top_of_cubic {A : Type*} [Group A] [Finite A] {n : ℕ}
    (h : FSource.TripleAlternating A n) (hn : 5 ≤ n) : generalizedFitting A = ⊤ := by
  let := cubic_quasisimple h hn
  let : IsQuasisimple (⊤ : Subgroup A) := IsQuasisimple.of_mulEquiv topEquiv.symm
  exact top_unique (component_le_generalizedFitting A ⊤
    ⟨(inferInstance : (⊤ : Subgroup A).Normal).isSubnormal,inferInstance⟩)

universe u v w
variable {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}
    (c : PointQuotientComparison ρ g)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))

include c in
/-- The component map either is faithful or kills the full cubic center,
with the induced alternating isomorphism compatible with the original map. -/
theorem point_cubic_component_kernel {n : ℕ}
    (h : FSource.TripleAlternating (generalizedFitting D) n) :
    Function.Injective g ∨
      (g.ker = (center (generalizedFitting D)).map (generalizedFitting D).subtype ∧
       ∃ e : generalizedFitting (offenderSubgroup ρ) ≃* alternatingGroup (Fin n),
         ∃ a : generalizedFitting D →* generalizedFitting (offenderSubgroup ρ),
           Function.Surjective a ∧ (∀ x, ((a x : offenderSubgroup ρ) : E) = g x) ∧
           ∀ x, e (a x) = h.quotient.some (QuotientGroup.mk' _ x)) := by
  let Z := (center (generalizedFitting D)).map (generalizedFitting D).subtype
  have hZ : Nat.card Z = 3 := by
    rw [card_map_of_injective Subtype.val_injective]
    exact cubic_card h
  rcases prime_subgroup_dichotomy c.kernel hZ with hk | hk
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff g).mp hk)
  · obtain ⟨_,_,a,ha,he,_⟩ := c.components
    have hak : a.ker = center (generalizedFitting D) := by
      ext x
      constructor
      · intro hx
        have hgx : g (x : D) = 1 := by
          rw [←he,MonoidHom.mem_ker.mp hx]
          rfl
        have hz : (x : D) ∈ Z := by
          change (x : D) ∈ (center (generalizedFitting D)).map (generalizedFitting D).subtype
          rw [←hk]
          exact hgx
        exact (mem_map_iff_mem Subtype.val_injective).mp hz
      · intro hx
        have hgx : g (x : D) = 1 := by
          apply MonoidHom.mem_ker.mp
          rw [hk]
          exact mem_map_of_mem _ hx
        apply MonoidHom.mem_ker.mpr
        apply Subtype.ext
        apply Subtype.ext
        change ((a x : offenderSubgroup ρ) : E) = 1
        rw [he]
        exact hgx
    obtain ⟨e,heq⟩ := quotient_equiv_of_kernel a ha _ hak h.quotient.some
    exact Or.inr ⟨hk,e,a,ha,he,heq⟩

include c b in
/-- A cubic A₇ component has order 7560, excluded from the bounded B.5
catalogue. Thus the actual map kills its full center and has A₇ component image. -/
theorem point_cubic_seven_kernel
    (h : FSource.TripleAlternating (generalizedFitting D) 7) :
    g.ker = (center (generalizedFitting D)).map (generalizedFitting D).subtype ∧
      Nonempty (generalizedFitting (offenderSubgroup ρ) ≃* alternatingGroup (Fin 7)) := by
  rcases point_cubic_component_kernel c h with hi | ⟨hk,e,_⟩
  · obtain ⟨_,_,a,ha,he,_⟩ := c.components
    have hai : Function.Injective a := by
      intro x y hxy
      apply Subtype.ext
      apply hi
      rw [←he,←he,hxy]
    let e := MulEquiv.ofBijective a ⟨hai,ha⟩
    have hmodel : FFAlternatives.QuasisimpleModel (generalizedFitting D) := by
      cases b.component.comap e with
      | linearTwo F _ _ e => exact .linearTwo F e
      | linearThree F _ e => exact .linearThree F e
      | alternatingSix e => exact .alternatingSix e
      | alternatingSeven e => exact .alternatingSeven e
      | tripleSix e q => exact .tripleSix e q
      | g2DerivedTwo e => exact .g2DerivedTwo e
      | linearFourTwo e => exact .linearFourTwo e
    apply (ComponentRows.TripleRows.model_card_ne_7560 hmodel _).elim
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (generalizedFitting D)),
      Nat.card_congr h.quotient.some.toEquiv,cubic_card h,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · exact ⟨hk,⟨e⟩⟩

private theorem symmetric_fitting {A : Type*} [Group A] [Finite A] {n : ℕ}
    (h : FSource.TripleSymmetric A n) (hn : n = 6 ∨ n = 7)
    (hcore : pCore 2 A = ⊥) : generalizedFitting A = commutator A := by
  let := h.normal
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsQuasisimple (commutator A) := cubic_quasisimple h.derived (by omega)
  have hc : Nat.card (commutator A) = (n.factorial / 2) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (commutator A)),
      Nat.card_congr h.derived.quotient.some.toEquiv,cubic_card h.derived,
      nat_card_alternatingGroup,Nat.card_fin]
  have hd : Nat.card A = n.factorial * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup h.kernel,
      Nat.card_congr h.quotientEquiv.toEquiv,Nat.card_congr h.kernelEquiv.toEquiv,
      Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)),Fintype.card_perm,Fintype.card_fin]
    simp [FSource.C]
  have hi : (commutator A).index = 2 := by
    have hm := (commutator A).card_mul_index
    rw [hc,hd] at hm
    rcases hn with rfl | rfl <;> norm_num [Nat.factorial] at hm <;> omega
  apply generalizedFitting_eq_of_quasisimple_two_quotient _ ?_ hcore
  apply IsPGroup.iff_card.mpr
  exact ⟨1,by simpa only [pow_one,←index_eq_card] using hi⟩

include c in
/-- The full alternating cover either survives the original surjection
or gives its literal central quotient with a commuting quotient square. -/
theorem point_cubic_alternating {n : ℕ} (hn : 5 ≤ n)
    (hg : Function.Surjective g) (h : FSource.TripleAlternating D n) :
    Function.Injective g ∨
      (g.ker = center D ∧ ∃ e : E ≃* alternatingGroup (Fin n),
        ∀ x : D, e (g x) = h.quotient.some (QuotientGroup.mk' _ x)) := by
  have ht := fitting_top_of_cubic h hn
  have hk : g.ker ≤ center D := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := c.kernel hx
    apply mem_center_iff.mpr
    intro y
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨y,ht.symm ▸ mem_top y⟩)
  rcases prime_subgroup_dichotomy hk (cubic_card h) with hk | hk
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff g).mp hk)
  · exact Or.inr ⟨hk,quotient_equiv_of_kernel g hg _ hk h.quotient.some⟩

include c in
/-- The full symmetric cover either survives or maps onto its original
symmetric quotient. The sign-action kernel is retained exactly. -/
theorem point_cubic_symmetric {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hg : Function.Surjective g) (hcore : pCore 2 D = ⊥)
    (h : FSource.TripleSymmetric D n) :
    letI := h.normal
    Function.Injective g ∨
      (g.ker = h.kernel ∧ ∃ e : E ≃* Equiv.Perm (Fin n),
        ∀ x : D, e (g x) = h.quotientEquiv (QuotientGroup.mk' _ x)) := by
  let := h.normal
  have hk := c.kernel
  rw [symmetric_fitting h hn hcore,h.center_eq] at hk
  have hz : Nat.card h.kernel = 3 := by
    rw [Nat.card_congr h.kernelEquiv.toEquiv]
    simp [FSource.C]
  rcases prime_subgroup_dichotomy hk hz with hk | hk
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff g).mp hk)
  · exact Or.inr ⟨hk,quotient_equiv_of_kernel g hg _ hk h.quotientEquiv⟩

include c b in
/-- The covered F.6.18(7) branch has actual action quotient A₇.
Its nontrivial kernel is the whole original center. -/
theorem point_cubic_alternating_seven
    (hg : Function.Surjective g) (h : FSource.TripleAlternating D 7) :
    g.ker = center D ∧ ∃ e : E ≃* alternatingGroup (Fin 7),
      ∀ x : D, e (g x) = h.quotient.some (QuotientGroup.mk' _ x) := by
  rcases point_cubic_alternating c (by decide) hg h with hi | h
  · let a : generalizedFitting D ≃* D :=
      (MulEquiv.subgroupCongr (fitting_top_of_cubic h (by decide))).trans topEquiv
    have hc := ComponentRows.tripleAlternating_of_equiv a h
    have hk := (point_cubic_seven_kernel c b hc).1
    have hz : Nat.card g.ker = 3 := by
      rw [hk,card_map_of_injective Subtype.val_injective]
      exact cubic_card hc
    rw [(MonoidHom.ker_eq_bot_iff g).mpr hi,card_bot] at hz
    omega
  · exact h

include c b in
/-- The covered F.6.18(9) branch has actual action quotient S₇.
Its nontrivial kernel is the original cubic sign-action kernel. -/
theorem point_cubic_symmetric_seven
    (hg : Function.Surjective g) (hcore : pCore 2 D = ⊥)
    (h : FSource.TripleSymmetric D 7) :
    letI := h.normal
    g.ker = h.kernel ∧ ∃ e : E ≃* Equiv.Perm (Fin 7),
      ∀ x : D, e (g x) = h.quotientEquiv (QuotientGroup.mk' _ x) := by
  let := h.normal
  rcases point_cubic_symmetric c (Or.inr rfl) hg hcore h with hi | h
  · let a : generalizedFitting D ≃* commutator D :=
      MulEquiv.subgroupCongr (symmetric_fitting h (Or.inr rfl) hcore)
    have hc := ComponentRows.tripleAlternating_of_equiv a h.derived
    have hk := (point_cubic_seven_kernel c b hc).1
    have hz : Nat.card g.ker = 3 := by
      rw [hk,card_map_of_injective Subtype.val_injective]
      exact cubic_card hc
    rw [(MonoidHom.ker_eq_bot_iff g).mpr hi,card_bot] at hz
    omega
  · exact h

/-- The four cubic-cover branches retain the original center or sign kernel.
An isomorphism in the faithful branch is the original comparison map. -/
structure PointCubicComparison
    {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    (g : D →* E) : Prop where
  alternating_six : ∀ h : FSource.TripleAlternating D 6,
    (∃ e : D ≃* E, ∀ x, e x = g x) ∨
      (g.ker = center D ∧ ∃ e : E ≃* alternatingGroup (Fin 6),
        ∀ x : D, e (g x) = h.quotient.some (QuotientGroup.mk' _ x))
  alternating_seven : ∀ h : FSource.TripleAlternating D 7,
    g.ker = center D ∧ ∃ e : E ≃* alternatingGroup (Fin 7),
      ∀ x : D, e (g x) = h.quotient.some (QuotientGroup.mk' _ x)
  symmetric_six : ∀ h : FSource.TripleSymmetric D 6,
    letI := h.normal
    (∃ e : D ≃* E, ∀ x, e x = g x) ∨
      (g.ker = h.kernel ∧ ∃ e : E ≃* Equiv.Perm (Fin 6),
        ∀ x : D, e (g x) = h.quotientEquiv (QuotientGroup.mk' _ x))
  symmetric_seven : ∀ h : FSource.TripleSymmetric D 7,
    letI := h.normal
    g.ker = h.kernel ∧ ∃ e : E ≃* Equiv.Perm (Fin 7),
      ∀ x : D, e (g x) = h.quotientEquiv (QuotientGroup.mk' _ x)

include c b in
/-- Compare every original cubic cover on the actual solvable-kernel map,
without replacing either cover by its simple quotient prematurely. -/
theorem point_cubic_comparison (hg : Function.Surjective g) (hcore : pCore 2 D = ⊥) :
    PointCubicComparison g := by
  refine ⟨?_,point_cubic_alternating_seven c b hg,?_,
    point_cubic_symmetric_seven c b hg hcore⟩
  · intro h
    rcases point_cubic_alternating c (by decide) hg h with hi | hk
    · exact Or.inl ⟨MulEquiv.ofBijective g ⟨hi,hg⟩,fun _ => rfl⟩
    · exact Or.inr hk
  · intro h
    rcases point_cubic_symmetric c (Or.inl rfl) hg hcore h with hi | hk
    · exact Or.inl ⟨MulEquiv.ofBijective g ⟨hi,hg⟩,fun _ => rfl⟩
    · exact Or.inr hk

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization


