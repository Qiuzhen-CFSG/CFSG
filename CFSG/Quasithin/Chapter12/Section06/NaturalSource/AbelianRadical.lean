module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianComponent
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightPointPrimeExclusion
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SolvableMutualCommutator

/-!
# Excluding normal odd radicals in the original abelian actor

The full original point stabilizer has order dividing1152. A two-perfect
two-by-p subgroup X, p>3, therefore centralizes V once 12.6.29 puts XT in M.
The original kernel bridge gives [X,L]≤O₂(L). Taking O² of XO₂(L) recovers
X and proves L normalizes X. Local characteristic two then forces the
intrinsic O₂(X) to be trivial, since it lies in the already trivial O₂(LTH).
Self-centralization of O₂(X) finishes X=1.

All earlier point, Sylow, TI, intersection and nonsingular-centralizer inputs
remain explicit. Source: Aschbacher--Smith, 12.6.30(3), printed p.835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

theorem SourceHypothesis.original_point_permutation_stabilizer_card_dvd
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    Nat.card (BinaryNaturalDual.VectorStabilizers.representationStabilizer (naturalRepresentation (Fin 8)) (D.fullCoordinates hZ z).toAdd) ∣ 1152 := by
  let E := D.fullSetup hZ T z
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let q : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker)
  have hq : Function.Surjective q := D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let fA := q.comp e.toMonoidHom
  let Q := P.mapSurjective (f := fA) (hq.comp e.surjective)
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val (D.fullCoordinates hZ z).toAdd =
        (D.fullCoordinates hZ z).toAdd := by
    rintro g ⟨a,ha,rfl⟩
    have hat : (e a : G) ∈ (T : Subgroup G) := by rw [hP] at ha; exact ha
    have he : conjugation L V S.chosen.normalizes (e a) z = z := by
      apply Subtype.ext
      have hh := hTC hat z.val (mem_zpowers _)
      change (e a : G)*z.val*(e a : G)⁻¹=z.val
      rw [←hh,mul_inv_cancel_right]
    exact (D.fullCoordinates_equivariant hZ (e a) z).symm.trans
      (congrArg (fun v : V => (D.fullCoordinates hZ v).toAdd) he)
  have hn : (D.fullCoordinates hZ z).toAdd ≠ 0 := by
    intro he
    exact hz ((D.fullCoordinates hZ).injective (he.trans (D.fullCoordinates hZ).map_one.symm))
  exact Eight.sylow_fixed_stabilizer_card_dvd Q (D.fullCoordinates hZ z).toAdd hn hfix

/-- The original point stabilizer kills every two-perfect two-by-p actor
with p>3. This uses the full original V and its literal conjugation. -/
theorem SourceHypothesis.original_large_prime_point_subgroup_centralizes
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (A : Subgroup G) (hA : IsPPerfect 2 A)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hq : IsPGroup p (A ⧸ pCore 2 A))
    (hAM : A ≤ M L) (hAz : A ≤ (D.fullSetup hZ T z).Gz) :
    A ≤ centralizer (V : Set G) := by
  let E := D.fullSetup hZ T z
  have hAN : A ≤ normalizer (V : Set G) := by
    intro x hx
    apply Mv_le_module_normalizer_of_TI hTI z hz
    exact ⟨hAM hx,by
      have hh : x ∈ E.Gz := hAz hx
      rwa [E.Gz_eq] at hh⟩
  obtain ⟨f,_,hf⟩ := S.original_normalizer_permutation_action D hZ hTV
  let C := BinaryNaturalDual.VectorStabilizers.representationStabilizer
    (naturalRepresentation (Fin 8)) (D.fullCoordinates hZ z).toAdd
  have ha (a : A) : V.normalizerMonoidHom ⟨a.val,hAN a.property⟩ z = z := by
    apply Subtype.ext
    have hh := hAz a.property z.val (mem_zpowers _)
    change a.val*z.val*a.val⁻¹=z.val
    rw [←hh,mul_inv_cancel_right]
  let g : A →* C := (f.comp (inclusion hAN)).codRestrict _ (fun a => by
    change naturalRepresentation (Fin 8) (f ⟨a.val,hAN a.property⟩)
      (D.fullCoordinates hZ z).toAdd = (D.fullCoordinates hZ z).toAdd
    rw [←hf,ha])
  have hg := Eight.hom_eq_one_of_large_prime_twoCore_quotient hp hA hq
    (S.original_point_permutation_stabilizer_card_dvd D hZ z hz hTz) g
  intro a ha v hv
  have hg' : f ⟨a,hAN ha⟩ = 1 := congrArg (fun k : A →* C => (k ⟨a,ha⟩).val) hg
  have he := hf ⟨a,hAN ha⟩ ⟨v,hv⟩
  rw [hg',map_one,Module.End.one_apply] at he
  have hh := congrArg (fun x : V => x.val) ((D.fullCoordinates hZ).injective he)
  change a*v*a⁻¹=v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The original H has no nontrivial normal two-perfect two-by-p
subgroup for p>3. Solvable containment, point action, and two-residual
recovery force a nontrivial two-core in LTH. -/
theorem SourceHypothesis.original_no_normal_large_prime_radical
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    {X : Subgroup G} (hXH : X ≤ H) (hHX : H ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hq : IsPGroup p (X ⧸ pCore 2 X)) : X = ⊥ := by
  let E := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := hTH.trans hHX
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (X ⧸ pCore 2 X) := hq.isNilpotent
  let : Group.IsSolvable X := (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
    ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (X ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes X T hTX
  have hXM : X ≤ M L := le_sup_left.trans
    (S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns le_sup_right)
  have hXC := S.original_large_prime_point_subgroup_centralizes D hZ z hz hTV hTz hTI
    X hX hp hq hXM (hXH.trans hH.2.1)
  have hcomm : ⁅X,L⁆ ≤ L.pCoreIn 2 := by
    rw [←S.centralizer_eq_core]
    apply le_inf
    · exact le_normalizer_iff_commutator_le_right.mp hXM
    · exact (commutator_mono hXC le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (S.chosen.normalizes.trans (normalizer_le_normalizer_centralizer _)))
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (S.chosen.sylow_normalizes_component.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hres := embedded_pResidual_join_pGroup X (L.pCoreIn 2) hX
    (isPGroup_pCoreIn 2 L) (hQT.trans hTX)
  have hLX : L ≤ normalizer (X : Set G) := by
    rw [←hres]
    exact (normalizes_sup_of_displacement L X (L.pCoreIn 2)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) hcomm).trans
        (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  have hcharH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←S.point_local_characteristic D hZ z hH]
    exact centralizer_generalizedFitting_le H
  let : (X.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHX
  have hcharX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hXH)).mp
      (normal_core_selfCentralizing hcharH (X.subgroupOf H))
  let J := L ⊔ (T : Subgroup G) ⊔ H
  have hJC : J ≤ normalizer (X.pCoreIn 2 : Set G) :=
    (sup_le (sup_le hLX hTX) hHX).trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hCJ : X.pCoreIn 2 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 X) ((pCoreIn_le 2 X).trans (hXH.trans le_sup_right)) hJC
  have hzJ : J.pCoreIn 2 = ⊥ := by
    change (pCore 2 J).map J.subtype = ⊥
    rw [S.point_join_core_eq_bot D hZ z hH,Subgroup.map_bot]
  have hcX : pCore 2 X = ⊥ :=
    ((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp
      (bot_unique (hCJ.trans_eq hzJ))
  apply bot_unique
  intro x hx
  have hh : (⟨x,hx⟩ : X) ∈ pCore 2 X := hcharX (by
    intro y hy
    have hy' : y = 1 := mem_bot.mp (hcX ▸ hy)
    simp only [hy',one_mul,mul_one])
  have hx1 : (⟨x,hx⟩ : X) = 1 := mem_bot.mp (hcX ▸ hh)
  exact congrArg (fun a : X => (a : G)) hx1

end CFSG.Quasithin.Chapter12.Section06
