module

public import Theory.AlgebraicGroup.Borel.SemisimpleCenter
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# The common root kernel and the semisimple center

The root-weight conjugation equation shows that a torus point annihilated by
all roots centralizes every realized root subgroup. It centralizes the torus
by commutativity. Generation by these subgroups therefore makes it central in
the ambient group, whose center is finite under semisimplicity.

The generation equality is kept explicit: GLS3, Theorem 1.9.5(i), supplies this
geometric step in the source argument for Proposition 1.14.1(a). These lemmas
do not assume that a maximal torus is self-centralizing.
Source: `refs/KGroup/GLS3/Chapter1.tex`, Sections 1.9, 1.12 and 1.14.
-/

public section

universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

omit [IsAlgClosed k] in
/-- If roots and the torus generate, a torus point annihilated by every root is central. -/
lemma rootWeightKernel_le_center_of_rootGeneration (D : RootGroupData G T)
    (hD : D.IsRealization) (hT : IsSubtorus T)
    (hgen : RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤)
    (t : Variety.Point T.carrierVariety)
    (ht : ∀ a, (D.rootWeight a).pointCharacter t = 1) :
    T.includePoint t ∈ Subgroup.center (Variety.Point G) := by
  let Z := Subgroup.centralizer ({T.includePoint t} : Set (Variety.Point G))
  have hroots : RootSubgroupGenerated D Set.univ ≤ Z := by
    apply RootSubgroupGenerated_le_of_rootSubgroup_le
    intro a _ g hg
    let X := D.rootSubgroup a
    let x : OneParameterParametrization X.carrierVariety :=
      Classical.choice (hD.2.2.1 a).1.2
    let y : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨g, hg⟩
    let s : k := Multiplicative.toAdd (additiveGroupPointEquiv k (x.inv.onPoints y))
    have hvalue : X.includePoint (x.value s) = g := by
      have hplus : kPlusPoint s = x.inv.onPoints y := by
        apply (additiveGroupPointEquiv k).injective
        rfl
      change X.includePoint (x.hom.onPoints (kPlusPoint s)) = g
      rw [hplus, x.inv_hom_id]
      exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨g, hg⟩)
    have heq := (hD.2.2.1 a).2 x s t
    rw [ht a, one_mul] at heq
    change (T.includePoint t)⁻¹ * X.includePoint (x.value s) *
      T.includePoint t = X.includePoint (x.value s) at heq
    rw [hvalue] at heq
    change g ∈ Subgroup.centralizer ({T.includePoint t} : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc
      T.includePoint t * g =
          T.includePoint t * ((T.includePoint t)⁻¹ * g * T.includePoint t) := by
            rw [heq]
      _ = g * T.includePoint t := by simp [mul_assoc]
  have htorus : T.toSubgroup ≤ Z := by
    intro g hg
    let y : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨g, hg⟩
    have hy : T.includePoint y = g :=
      congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨g, hg⟩)
    rw [← hy]
    change T.includePoint y ∈
      Subgroup.centralizer ({T.includePoint t} : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (isMulCommutative_iff.mp hT.isMulCommutative) y t
    exact (T.inclusion.onPoints.map_mul y t).symm.trans
      ((congrArg T.inclusion.onPoints hcomm).trans (T.inclusion.onPoints.map_mul t y))
  have htop : (⊤ : Subgroup (Variety.Point G)) ≤ Z := by
    rw [← hgen]
    exact sup_le hroots htorus
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))

/-- Semisimplicity makes the common root kernel finite once roots and the torus generate. -/
lemma rootWeightKernel_finite_of_rootGeneration (D : RootGroupData G T)
    (hD : D.IsRealization) (hT : IsSubtorus T)
    (hsemi : IsSemisimpleAlgebraicGroup G)
    (hgen : RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤) :
    {t : Variety.Point T.carrierVariety |
      ∀ a, (D.rootWeight a).pointCharacter t = 1}.Finite := by
  have := connectedSemisimple_center_finite hsemi
  have hz : (Subgroup.center (Variety.Point G) : Set (Variety.Point G)).Finite :=
    Set.toFinite _
  apply (hz.preimage T.inclusion_injective.injOn).subset
  intro t ht
  exact rootWeightKernel_le_center_of_rootGeneration D hD hT hgen t ht

end Theory.AlgebraicGroup
