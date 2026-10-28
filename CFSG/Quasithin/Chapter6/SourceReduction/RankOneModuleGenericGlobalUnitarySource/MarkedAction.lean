module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySecondParabolic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction
public import Theory.GroupTheory.Amalgam.AutomorphismTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Graph

/-!
# The full common normalizer acting on the native unitary pair

Let R = T ∩ L and D = N_G(L) ∩ N_G(O²(H)). The proved source local
conditions give D = N_G(R). Hence D normalizes both reduced source
parabolics and their whole intersection. Conjugation on this pair is
faithful: its kernel centralizes the residual join, whose ambient
centralizer is trivial. Transport by the literal three comparison maps
constructs a faithful action on the native marked unitary amalgam.

The ordinary U₄ row has sourceS = R; the degree-two row uses its proved
O²-restriction to the ordinary pair. Both orientations are retained, with
m > 1 and n = 2m. The U₅(4) row uses its actual projective carrier and
index-three residual quotients. On the full reduced overlap the action
is the native Borel-inner action, and faithfulness proves the exact converse.
Intersecting this overlap with the original T gives precisely R. Consequently
the original degree-two graph involution remains an involution outside the
Borel-inner action range; neither sourceS nor T is replaced by R.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659, and the setup of
F.4.37, printed p.293 of `refs/quasithin.pdf`. This constructs actions on
the concrete marked pair, not automorphisms of its simple completion.
The simultaneous extension of these actions, ambient Sylow placement and
outer transfer, F.4.42 containment, and full-extension order comparison
remain further obligations. No recognition of the residual join is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace UnitarySource
variable {G : Type*} [Group G]

private theorem normalizes_parabolic {N S : Subgroup G} {J : Fin 2 → Subgroup G}
    (hNS : N ≤ normalizer (S : Set G))
    (hNJ : ∀ i, N ≤ normalizer (J i : Set G)) (i : Fin 2) :
    N ≤ normalizer (ChapterF.Source.parabolic J S i : Set G) := by
  have hb (j : Fin 2) : N ≤ normalizer (ChapterF.Source.borel (J j) S : Set G) := by
    have hi := (le_inf hNS (hNJ j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hNJ j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hNJ i) hNS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hb (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

private def conjugationPair (P Q N : Subgroup G)
    (hP : N ≤ normalizer (P : Set G)) (hQ : N ≤ normalizer (Q : Set G)) :
    N →* RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right) where
  toFun g :=
    { left := P.normalizerMonoidHom (inclusion hP g)
      middle := (P ⊓ Q).normalizerMonoidHom
        (inclusion ((le_inf hP hQ).trans inf_normalizer_le_normalizer_inf) g)
      right := Q.normalizerMonoidHom (inclusion hQ g)
      left_commutes _ := Subtype.ext rfl
      right_commutes _ := Subtype.ext rfl }
  map_one' := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp
  map_mul' a b := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp [mul_assoc]

/-- Conjugation by the entire marked middle, on both endpoints. -/
@[expose] def innerMiddle {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (β : RankTwoAmalgam X Y Z) : Y →* RankTwoAmalgam.Iso β β where
  toFun b :=
    { left := MulAut.conj (β.left b)
      middle := MulAut.conj b
      right := MulAut.conj (β.right b)
      left_commutes x := by simp only [MulAut.conj_apply,map_mul,map_inv]
      right_commutes x := by simp only [MulAut.conj_apply,map_mul,map_inv] }
  map_one' := by apply RankTwoAmalgam.Iso.ext <;> simp
  map_mul' a b := by apply RankTwoAmalgam.Iso.ext <;> simp

/-- A genuine action of the full common normalizer on a specified marked pair.
The source parameter S is recorded separately from the ambient Sylow. -/
structure MarkedMiddleAction (L K S : Subgroup G)
    {X Y Z : Type*} [Group X] [Group Y] [Group Z] (β : RankTwoAmalgam X Y Z) where
  comparison : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β
  middle_le : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
    ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) ≤
      normalizer (L : Set G) ⊓ normalizer (K : Set G)
  action : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
    RankTwoAmalgam.Iso β β
  faithful : Function.Injective action
  left_conjugation : ∀ g x,
    (comparison.left.symm ((action g).left x)).val =
      g.val * (comparison.left.symm x).val * g.val⁻¹
  middle_conjugation : ∀ g x,
    (comparison.middle.symm ((action g).middle x)).val =
      g.val * (comparison.middle.symm x).val * g.val⁻¹
  right_conjugation : ∀ g x,
    (comparison.right.symm ((action g).right x)).val =
      g.val * (comparison.right.symm x).val * g.val⁻¹

namespace MarkedMiddleAction
variable {L K S : Subgroup G}
  {X Y Z : Type*} [Group X] [Group Y] [Group Z] {β : RankTwoAmalgam X Y Z}

/-- Every element of the full reduced overlap induces exactly its native
inner marked action, including the odd Cartan elements. -/
theorem inner_action (a : MarkedMiddleAction L K S β)
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    a.action (inclusion a.middle_le b) = innerMiddle β (a.comparison.middle b) := by
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.left.symm ((a.action (inclusion a.middle_le b)).left x) =
        (sourceParabolicAmalgam ![L,K] S).left b * a.comparison.left.symm x *
          ((sourceParabolicAmalgam ![L,K] S).left b)⁻¹ :=
      Subtype.ext (a.left_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.left hx
    change (a.action (inclusion a.middle_le b)).left x =
      β.left (a.comparison.middle b) * x * (β.left (a.comparison.middle b))⁻¹
    simpa only [map_mul,map_inv,a.comparison.left_commutes,
      a.comparison.left.apply_symm_apply] using hh
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.middle.symm ((a.action (inclusion a.middle_le b)).middle x) =
        b * a.comparison.middle.symm x * b⁻¹ :=
      Subtype.ext (a.middle_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.middle hx
    change (a.action (inclusion a.middle_le b)).middle x =
      a.comparison.middle b * x * (a.comparison.middle b)⁻¹
    simpa only [map_mul,map_inv,a.comparison.middle.apply_symm_apply] using hh
  · apply MulEquiv.ext
    intro x
    have hx : a.comparison.right.symm ((a.action (inclusion a.middle_le b)).right x) =
        (sourceParabolicAmalgam ![L,K] S).right b * a.comparison.right.symm x *
          ((sourceParabolicAmalgam ![L,K] S).right b)⁻¹ :=
      Subtype.ext (a.right_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg a.comparison.right hx
    change (a.action (inclusion a.middle_le b)).right x =
      β.right (a.comparison.middle b) * x * (β.right (a.comparison.middle b))⁻¹
    simpa only [map_mul,map_inv,a.comparison.right_commutes,
      a.comparison.right.apply_symm_apply] using hh

/-- The native Borel-inner preimage is precisely the original reduced overlap. -/
theorem inner_preimage (a : MarkedMiddleAction L K S β)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    a.action g ∈ (innerMiddle β).range ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
        ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  constructor
  · rintro ⟨c,hc⟩
    let b := a.comparison.middle.symm c
    have he : a.action (inclusion a.middle_le b) = a.action g := by
      rw [a.inner_action]
      dsimp only [b]
      rw [a.comparison.middle.apply_symm_apply]
      exact hc
    have hv := congrArg Subtype.val (a.faithful he)
    exact hv ▸ b.property
  · intro hg
    exact ⟨a.comparison.middle ⟨g.val,hg⟩,(a.inner_action ⟨g.val,hg⟩).symm⟩
end MarkedMiddleAction

variable [Finite G]
/-- Full-normalizer conjugation on the actual reduced pair is faithful.
Only the already established source local conditions are used. -/
theorem marked_middle_action_of_local_conditions
    {L K R : Subgroup G}
    (h : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L K) L K R)
    (hPL : ∀ i : Fin 2, ChapterF.Source.parabolic ![L,K] R i ≤
      normalizer (![L,K] i : Set G))
    {X Y Z : Type*} [Group X] [Group Y] [Group Z] {β : RankTwoAmalgam X Y Z}
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] R) β) :
    Nonempty (MarkedMiddleAction L K R β) := by
  let N := normalizer (L : Set G) ⊓ normalizer (K : Set G)
  let P := ChapterF.Source.parabolic ![L,K] R
  have hNS : N ≤ normalizer (R : Set G) := h.normalizer_eq_middle.ge
  have hNP (i : Fin 2) : N ≤ normalizer (P i : Set G) := by
    apply normalizes_parabolic hNS
    intro j
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  let ρ := conjugationPair (P 0) (P 1) N (hNP 0) (hNP 1)
  have hf : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply bot_unique
    intro g hg
    have heq : ρ g = 1 := hg
    have hcP : g.val ∈ centralizer (P 0 : Set G) ∧ g.val ∈ centralizer (P 1 : Set G) := by
      constructor
      · intro x hx
        have hh := congrArg (fun a => ((a.left ⟨x,hx⟩ : P 0) : G)) heq
        change g.val*x*g.val⁻¹=x at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      · intro x hx
        have hh := congrArg (fun a => ((a.right ⟨x,hx⟩ : P 1) : G)) heq
        change g.val*x*g.val⁻¹=x at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hc : L ⊔ K ≤ centralizer ({g.val} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (hcP.1 x
          ((show L ≤ P 0 from le_sup_left.trans le_sup_left) hx))
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (hcP.2 x
          ((show K ≤ P 1 from le_sup_left.trans le_sup_left) hx))
    have hgC : g.val ∈ centralizer ((L ⊔ K : Subgroup G) : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hc hx)
    rw [normalizer_pair_centralizer_eq_bot h] at hgC
    exact Subtype.ext (mem_bot.mp hgC)
  let σ := (RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp ρ
  refine ⟨⟨e,le_inf (inf_le_left.trans (hPL 0)) (inf_le_right.trans (hPL 1)),
    σ,(RankTwoAmalgam.automorphismConjEquiv e).injective.comp hf,?_,?_,?_⟩⟩
  · intro g x
    change (e.left.symm (e.left ((ρ g).left (e.left.symm x)))).val = _
    rw [e.left.symm_apply_apply]
    rfl
  · intro g x
    change (e.middle.symm (e.middle ((ρ g).middle (e.middle.symm x)))).val = _
    rw [e.middle.symm_apply_apply]
    rfl
  · intro g x
    change (e.right.symm (e.right ((ρ g).right (e.right.symm x)))).val = _
    rw [e.right.symm_apply_apply]
    rfl

end UnitarySource

namespace UnitarySource
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

private theorem two_subgroup_le_residual_of_perfect
    {X : Type*} [Group X] (P K : Subgroup X) [Group.IsPerfect K]
    (hKP : K ≤ P) (U : Subgroup P)
    (hU : U.map P.subtype ≤ K) : U ≤ solvableResidual P := by
  have hh := hU.trans (le_map_solvableResidual_of_isPerfect K P hKP)
  exact (map_le_map_iff_of_injective P.subtype_injective).mp hh

private theorem point_two_subgroup (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
    (U : Subgroup (pointParabolic m hm)) (hU : IsPGroup 2 U) :
    U ≤ solvableResidual _ := by
  let := PointLocal.projectiveLocal_isPerfect m hm hm'
  apply two_subgroup_le_residual_of_perfect _ (PointLocal.ProjectiveLocal m hm)
    (by rw [←PointLocal.pointParabolic_solvableResidual m hm hm']; exact map_subtype_le _) U
  exact PointLocal.twoSubgroup_le_projectiveLocal m hm _ (hU.map _) (map_subtype_le _)

private theorem plane_two_subgroup (m : ℕ) (hm : 1 ≤ m)
    (U : Subgroup (planeParabolic m hm)) (hU : IsPGroup 2 U) :
    U ≤ solvableResidual _ := by
  let := L2_isPerfect m hm
  exact two_subgroup_le_residual_of_perfect _ (L2 m hm) (L2_le_planeParabolic m hm) U
    (two_subgroup_le_L2 m hm _ (hU.map _) (map_subtype_le _))

private theorem two_subgroup_transport {P K S : Subgroup G}
    (hr : (solvableResidual P).map P.subtype = K)
    (hS : IsPGroup 2 S) (hSP : S ≤ P)
    {X : Type*} [Group X] (e : P ≃* X)
    (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) : S ≤ K := by
  have hh := hb ((S.subgroupOf P).map e.toMonoidHom)
    (hS.comap_subtype.map e.toMonoidHom)
  rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,
    map_le_map_iff_of_injective e.injective] at hh
  have hm := map_mono (f := P.subtype) hh
  rw [map_subgroupOf_eq_of_le hSP,hr] at hm
  exact hm
end UnitarySource

open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- In either ordinary orientation the source Sylow is the reduced Sylow.
The degree-two row is deliberately absent from this equality. -/
theorem Preparation.unitary_ordinary_sourceS_eq
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) :
    sourceS L H = (T : Subgroup G) ⊓ L := by
  have hm' := (d.unitary_local_structure h hTH hp m hm hc).1
  have hs : sourceS L H ≤ L := by
    have ht {X : Type} [Group X]
        (e : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ≃* X)
        (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) : sourceS L H ≤ L :=
      UnitarySource.two_subgroup_transport (d.parabolic_residuals h hTH hp 0)
      (pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H))
      (show sourceS L H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
        from le_sup_right.trans le_sup_left) e hb
    rcases hc with hc | hc <;> obtain ⟨e⟩ := hc
    · exact ht e.left (UnitarySource.point_two_subgroup m hm hm')
    · exact ht e.left (UnitarySource.plane_two_subgroup m hm)
  exact (inf_eq_left.mpr hs).symm.trans d.left_intersection

/-- Both original four-dimensional rows supply the ordinary reduced comparison,
retaining the full reduced overlap and both residual embeddings. -/
theorem Preparation.unitary_reduced_native_comparison
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse)) := by
  rcases hc with ho | he
  · have hs := d.unitary_ordinary_sourceS_eq h hTH hp m hm ho
    have hm' := d.unitary_local_structure h hTH hp m hm ho
    exact ⟨hm'.1,hm'.2.1,hs ▸ ho⟩
  · have hm' := d.unitaryExtension_local_structure h hTH hp m hm he
    exact ⟨hm'.1,hm'.2.1,d.unitaryExtension_reduced_amalgam h hTH hp m hm'.1 he⟩

private theorem reduced_parabolics_normalize
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (hc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,residual H] (sourceS L H)))
    (i : Fin 2) : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i ≤
      normalizer (![L,residual H] i : Set G) := by
  have hn : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ≤
      normalizer (![L,residual H] i : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show ![L,residual H] i ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
        from le_sup_left.trans le_sup_left)).mp
      ((d.hypothesisF11 h hTH).local_normal_in_parabolic i)
  rw [d.reduced_source_parabolics h hTH hp hc i]
  exact (map_subtype_le _).trans hn

/-- The full common normalizer acts faithfully on the native reduced unitary
pair. Both original comparisons and both orientations are retained. -/
theorem Preparation.unitary_native_middle_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
      (Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
        (amalgam m hm)) ∨
       Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
        (amalgam m hm).reverse)) := by
  obtain ⟨hm',hn,he⟩ := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  have hloc := d.unitary_normalizer_local_conditions h hH hp m hm hc
  have cc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
    hc.elim (.unitary m hm) (.unitaryExtension m hm)
  have hPL := reduced_parabolics_normalize d h hH.1.1.2 hp cc
  refine ⟨hm',hn,?_⟩
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · exact Or.inl (UnitarySource.marked_middle_action_of_local_conditions hloc hPL e)
  · exact Or.inr (UnitarySource.marked_middle_action_of_local_conditions hloc hPL e)

/-- The original ambient Sylow meets the whole reduced overlap in exactly
T ∩ L. In particular this does not identify the original ambient T with T ∩ L. -/
theorem Preparation.unitary_reduced_overlap_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    (T : Subgroup G) ⊓ (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) =
      (T : Subgroup G) ⊓ L := by
  obtain ⟨hm',_,he⟩ := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  have cc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
    hc.elim (.unitary m hm) (.unitaryExtension m hm)
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp cc 0
  have hle : (T : Subgroup G) ⊓ P 0 ≤ L := by
    have ht {X : Type} [Group X] (e : P 0 ≃* X)
        (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) :
        (T : Subgroup G) ⊓ P 0 ≤ L :=
      UnitarySource.two_subgroup_transport hr (T.isPGroup'.to_le inf_le_left)
        (show (T : Subgroup G) ⊓ P 0 ≤ P 0 from inf_le_right) e hb
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact ht e.left (UnitarySource.point_two_subgroup m hm hm')
    · exact ht e.left (UnitarySource.plane_two_subgroup m hm)
  exact le_antisymm (le_inf inf_le_left ((inf_le_inf_left _ inf_le_left).trans hle))
    (le_inf inf_le_left (le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)))

/-- In the five-dimensional row the actual source Sylow is the common
residual Sylow. This uses the odd index-three native residual quotients. -/
theorem Preparation.unitaryFive_sourceS_eq
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    sourceS L H = (T : Subgroup G) ⊓ L := by
  have hs : sourceS L H ≤ L := by
    have ht {X : Type} [Group X]
        (e : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ≃* X)
        (hb : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ solvableResidual X) : sourceS L H ≤ L :=
      UnitarySource.two_subgroup_transport (d.parabolic_residuals h hTH hp 0)
      (pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H))
      (show sourceS L H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
        from le_sup_right.trans le_sup_left) e hb
    rcases hc with hc | hc <;> obtain ⟨e⟩ := hc
    · apply ht e.left
      intro V hV
      exact IsPGroup.le_normal_of_index_primeTo U.leftLocal V hV
        (by rw [U.leftLocal_index_eq_three]; decide)
    · apply ht e.left
      intro V hV
      exact IsPGroup.le_normal_of_index_primeTo U.rightLocal V hV
        (by rw [U.rightLocal_index]; decide)
  exact (inf_eq_left.mpr hs).symm.trans d.left_intersection

/-- The full common normalizer acts on the actual projective U₅(4) pair.
The projective kernel of order five is retained by the original model. -/
theorem Preparation.unitaryFive_native_middle_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam) ∨
    Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse) := by
  have hloc := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have hPL := reduced_parabolics_normalize d h hH.1.1.2 hp (.unitaryFive U hc)
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  rw [hs] at hc
  rcases hc with hc | hc <;> obtain ⟨e⟩ := hc
  · exact Or.inl (UnitarySource.marked_middle_action_of_local_conditions hloc hPL e)
  · exact Or.inr (UnitarySource.marked_middle_action_of_local_conditions hloc hPL e)


/-- The degree-two graph element is an actual non-Borel-inner involution of
the native reduced marked pair. The full common normalizer acts faithfully,
so the graph element is retained when sourceS is reduced. -/
theorem Preparation.unitary_graph_native_middle_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ ∃ f : G,
      f ∈ sourceS L H ∧ f ∈ (T : Subgroup G) ∧ orderOf f = 2 ∧
      f ∉ L ∧ f ∉ residual H ∧
      ∃ hf : f ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G),
        (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
            (amalgam m hm),
          orderOf (a.action ⟨f,hf⟩) = 2 ∧
          a.action ⟨f,hf⟩ ∉ (UnitarySource.innerMiddle (amalgam m hm)).range) ∨
        (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
            (amalgam m hm).reverse,
          orderOf (a.action ⟨f,hf⟩) = 2 ∧
          a.action ⟨f,hf⟩ ∉ (UnitarySource.innerMiddle (amalgam m hm).reverse).range) := by
  obtain ⟨hm',hn,f,hfS,hfT,hf2,hfL,hfK,_⟩ :=
    d.unitary_graph_fixed_amalgam h hH hp m hm hc
  have hfD : f.val ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
    ⟨h.sylow_normalizes hfT,(hH.1.1.2.trans (le_normalizer_residual H)) hfT⟩
  have hC := d.unitary_reduced_overlap_sylow h hH hp m hm (Or.inr hc)
  have hnot : f.val ∉ (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) := by
    intro hmem
    exact hfL ((hC.le ⟨hfT,hmem⟩).2)
  have lift {X Y Z : Type} [Group X] [Group Y] [Group Z] {β : RankTwoAmalgam X Y Z}
      (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) β) :
      orderOf (a.action ⟨f.val,hfD⟩) = 2 ∧
        a.action ⟨f.val,hfD⟩ ∉ (UnitarySource.innerMiddle β).range := by
    refine ⟨?_, fun hh => hnot ((a.inner_preimage _).mp hh)⟩
    rw [orderOf_injective a.action a.faithful]
    exact (Subgroup.orderOf_coe ⟨f.val,hfD⟩).symm.trans hf2
  refine ⟨hm',hn,f.val,hfS,hfT,hf2,hfL,hfK,hfD,?_⟩
  rcases (d.unitary_native_middle_action h hH hp m hm (Or.inr hc)).2.2 with ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨a,lift a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr ⟨a,lift a⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
