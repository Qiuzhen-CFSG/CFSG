module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.ModuleCases
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalOvergroups
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Pulling marked five-dimensional parabolics back to the component

Full preimages under L → L/O₂(L) ≃ PSL₅(2) ≃ GL₅(2) are embedded in the
original ambient group. Joins, maximality inside L, and quotient maps are
preserved. Their intrinsic two-core quotients agree with those of the
model parabolics because the restriction map has a two-group kernel.
Inner action by S on the marked quotient fixes every parabolic containing
the image of S∩L, and gives the required relative normalization.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics
variable {G : Type*} [Group G] {L : Subgroup G}

/-- Full preimage in the original ambient group, using the specified marking. -/
noncomputable def lift (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) : Subgroup G :=
  (Q.comap (linearAction (by decide) e)).map L.subtype

theorem lift_le (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) : lift e Q ≤ L := map_subtype_le _

theorem lift_subgroupOf (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) :
    (lift e Q).subgroupOf L = Q.comap (linearAction (by decide) e) :=
  comap_map_eq_self_of_injective L.subtype_injective _

theorem linearAction_ker (e : (L ⧸ pCore 2 L) ≃* Projective 5) :
    (linearAction (by decide) e).ker = pCore 2 L := by
  unfold linearAction
  rw [MonoidHom.ker_comp_of_injective _ _
    ((projectiveEquivLinear (by decide : 0 < 5)).injective.comp e.injective),
    QuotientGroup.ker_mk']

theorem core_le_lift (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) : L.pCoreIn 2 ≤ lift e Q := by
  apply map_mono
  rw [← linearAction_ker e]
  intro l hl
  change linearAction (by decide) e l ∈ Q
  rw [MonoidHom.mem_ker.mp hl]
  exact Q.one_mem

theorem lift_top (e : (L ⧸ pCore 2 L) ≃* Projective 5) : lift e ⊤ = L := by
  rw [lift, comap_top, ← MonoidHom.range_eq_map, range_subtype]

theorem lift_sup (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q₁ Q₂ : Subgroup (LinearGroup 5)) :
    lift e (Q₁ ⊔ Q₂) = lift e Q₁ ⊔ lift e Q₂ := by
  rw [lift, ← comap_sup_eq _ _ _ (linearAction_surjective (by decide) e), Subgroup.map_sup]
  rfl

theorem le_lift {X : Subgroup G} (hXL : X ≤ L)
    (e : (L ⧸ pCore 2 L) ≃* Projective 5) (Q : Subgroup (LinearGroup 5))
    (hX : (X.subgroupOf L).map (linearAction (by decide) e) ≤ Q) : X ≤ lift e Q := by
  intro x hx
  exact mem_map.mpr ⟨⟨x, hXL hx⟩, hX (mem_map.mpr
    ⟨⟨x, hXL hx⟩, hx, rfl⟩), rfl⟩

theorem lift_isCoatom (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    {Q : Subgroup (LinearGroup 5)} (hQ : IsCoatom Q) :
    IsCoatom ((lift e Q).subgroupOf L) := by
  rw [lift_subgroupOf]
  exact isCoatom_comap_of_surjective (linearAction_surjective (by decide) e) hQ

noncomputable def liftMap (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) : lift e Q →* Q :=
  ((linearAction (by decide) e).comp (inclusion (lift_le e Q))).codRestrict Q (by
    intro x
    have hx : (⟨x.val, lift_le e Q x.property⟩ : L) ∈ (lift e Q).subgroupOf L := x.property
    rwa [lift_subgroupOf] at hx)

theorem liftMap_apply (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) (x : lift e Q) :
    (liftMap e Q x : LinearGroup 5) =
      linearAction (by decide) e (⟨x.val, lift_le e Q x.property⟩ : L) := rfl

theorem liftMap_surjective (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) : Function.Surjective (liftMap e Q) := by
  intro y
  obtain ⟨l, hl⟩ := linearAction_surjective (by decide) e y.val
  have hm : l ∈ Q.comap (linearAction (by decide) e) := by
    change linearAction (by decide) e l ∈ Q
    rw [hl]
    exact y.property
  exact ⟨⟨l.val, mem_map.mpr ⟨l, hm, rfl⟩⟩, Subtype.ext hl⟩

theorem liftMap_ker (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) :
    (liftMap e Q).ker = (pCore 2 L).comap (inclusion (lift_le e Q)) := by
  ext x
  change liftMap e Q x = 1 ↔ _
  rw [Subtype.ext_iff]
  change linearAction (by decide) e (inclusion (lift_le e Q) x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, linearAction_ker]
  rfl

theorem liftMap_ker_isTwoGroup (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) : IsPGroup 2 (liftMap e Q).ker := by
  rw [liftMap_ker]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective (lift_le e Q))

/-- Trivial diagram action, expressed on representatives of the actual
marked quotient. Each element of S acts by an inner model automorphism. -/
def IsInnerOnModel (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (S : Subgroup G) (hn : S ≤ normalizer (L : Set G)) : Prop :=
  ∀ s : S, ∃ g : LinearGroup 5, ∀ l : L,
    linearAction (by decide) e (L.normalizerMonoidHom (inclusion hn s) l) =
      g * linearAction (by decide) e l * g⁻¹

/-- Inner conjugation preserving the marked Sylow fixes every lifted flag.
All normality here is relative to S or to its join with the preimage. -/
theorem normalizes_lift_flag (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (S D : Subgroup G) (hDL : D ≤ L) (hn : S ≤ normalizer (L : Set G))
    (hnD : S ≤ normalizer (D : Set G)) (hi : IsInnerOnModel e S hn)
    (b : BinaryLinear.FiveFlagGeometry.FiveBasis)
    (hD : (D.subgroupOf L).map (linearAction (by decide) e) =
      BinaryLinear.FiveFlagGeometry.flagStabilizer b Set.univ)
    (cuts : Set (Fin 4)) :
    S ≤ normalizer (lift e (BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts) : Set G) := by
  apply le_normalizer_iff.mpr
  intro s hs x hx
  obtain ⟨g, hg⟩ := hi ⟨s, hs⟩
  let a := L.normalizerMonoidHom (inclusion hn ⟨s, hs⟩)
  have ha : (D.subgroupOf L).map a.toMonoidHom = D.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_map]
    have he : L.subtype.comp a.toMonoidHom = (MulAut.conj s).toMonoidHom.comp L.subtype := rfl
    rw [he, ← Subgroup.map_map, map_subgroupOf_eq_of_le hDL]
    exact mem_normalizer_iff_map_conj_eq.mp (hnD hs)
  have he : (linearAction (by decide) e).comp a.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (linearAction (by decide) e) := by
    apply MonoidHom.ext
    intro l
    exact hg l
  have hB : (BinaryLinear.FiveFlagGeometry.flagStabilizer b Set.univ).map
      (MulAut.conj g).toMonoidHom = BinaryLinear.FiveFlagGeometry.flagStabilizer b Set.univ := by
    rw [← hD, Subgroup.map_map, ← he, ← Subgroup.map_map, ha]
  have hQ : (BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts).map
      (MulAut.conj g).toMonoidHom = BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts :=
    BinaryLinear.InvariantNodeActions.inner_fixes_cutStabilizer b g hB cuts
  obtain ⟨l, hl, rfl⟩ := mem_map.mp hx
  refine mem_map.mpr ⟨a l, ?_, rfl⟩
  change linearAction (by decide) e (a l) ∈ BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts
  rw [hg l]
  have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show linearAction (by decide) e l ∈ BinaryLinear.FiveFlagGeometry.flagStabilizer b cuts from hl)
  rw [hQ] at hm
  exact hm

variable [Finite G]

/-- Quotienting the full preimage by its own two-core recovers the intrinsic
model quotient, rather than the quotient by the old O₂(L). -/
noncomputable def liftQuotientEquiv (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) :
    (lift e Q ⧸ pCore 2 (lift e Q)) ≃* (Q ⧸ pCore 2 Q) := by
  letI : Finite Q := Finite.of_surjective _ (liftMap_surjective e Q)
  let f := liftMap e Q
  let q := (QuotientGroup.mk' (pCore 2 Q)).comp f
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (liftMap_surjective e Q)
  have hk : q.ker = pCore 2 (lift e Q) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup (liftMap_surjective e Q) (liftMap_ker_isTwoGroup e Q)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

theorem liftQuotientEquiv_mk (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (Q : Subgroup (LinearGroup 5)) (x : lift e Q) :
    liftQuotientEquiv e Q (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (liftMap e Q x) := rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics

end
