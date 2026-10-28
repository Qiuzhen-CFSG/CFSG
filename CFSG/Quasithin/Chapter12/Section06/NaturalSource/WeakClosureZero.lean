module
public import Theory.Representation.BinaryPermutation.EightRigidity
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.IntersectingConjugates
public import CFSG.Quasithin.Chapter12.Section06.LocalAlternatives.WeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# The original zeroth weak closure in the fixed-free branch

Every nontrivial elementary subgroup of S8 moves a vector in the natural
six-space with orbit of size at most four. Its stabilizer has corank at
most two and a larger fixed space, proving the E.3.8 family A3 empty.
Pulling this calculation through the actual normalizer action gives the
same rigidity exclusion for the original actors, with their kernels retained.

By12.6.27, a noncommuting conjugate W of V is disjoint from V. Thus
V intersect N_G(W) centralizes W. The earlier corank-two centralizer control
would make W rigid at corank three if W lay in T, a contradiction. Hence
W0 centralizes V, and the original local uniqueness puts N_G(W0) in M.

This supplies12.6.28(1,3) and its literal weak-closure application under the
retained earlier geometry. The three-extension calculation and W1 bound
in12.6.28(2,4) remain separate obligations.

Source: Aschbacher--Smith,12.6.27--28, printed pp.833--835, and E.3.34.
-/

public section
open Subgroup BinaryPermutation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
/-- Source 12.6.28(1) on the intrinsic S8 natural module, using the actual
E.3.8 family and relative indices in the elementary actor. -/
theorem natural_fixedSpaceFamily_three_eq_empty :
    ChapterE.fixedSpaceFamily (naturalRepresentation (Fin 8)) 3 = ∅ := by
  classical
  let ρ := naturalRepresentation (Fin 8)
  let : MulAction (Equiv.Perm (Fin 8)) (natural (Fin 8)) := {
    smul := fun a v => ρ a v
    one_smul := by intro v; change ρ 1 v = v; simp
    mul_smul := by intro a b v; change ρ (a * b) v = ρ a (ρ b v); rw [map_mul,Module.End.mul_apply] }
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨a,ha,v,hv,hm⟩ := EightRigidity.moved_small_orbit A hA.2.1.1
  let B := A ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) v
  have hs : B.subgroupOf A = MulAction.stabilizer A v := by
    ext b
    change (b.val ∈ A ∧ ρ b.val v = v) ↔ ρ b.val v = v
    exact and_iff_right b.property
  have hi : B.relIndex A ≤ 4 := by
    rw [Subgroup.relIndex,hs,MulAction.index_stabilizer]
    exact hv
  have he := hA.2.2 B inf_le_left
    (lt_of_le_of_lt (Nat.log_mono_right hi) (by decide : Nat.log 2 4 < 3))
  have hb : v ∈ Representation.BinaryOffender.fixedSpace ρ B := by
    intro b
    exact b.property.2
  have hh : v ∈ Representation.BinaryOffender.fixedSpace ρ A := he.symm ▸ hb
  exact hm (hh ⟨a,ha⟩)

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem natural_orbit_centralizer_index
    {A : Subgroup G} (hn : A ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] natural (Fin 8))
    (f : A →* Equiv.Perm (Fin 8))
    (hE : ∀ a w, E (seedRepresentation A V hn a w) =
      naturalRepresentation (Fin 8) (f a) (E w)) (v : V) :
    (A ⊓ Gv (v : G)).relIndex A =
      Nat.card (Set.range fun a : f.range => naturalRepresentation (Fin 8) a.val (E (Additive.ofMul v))) := by
  let : MulAction A V := MulAction.compHom V (conjugation A V hn)
  have hs : (A ⊓ Gv (v : G)).subgroupOf A = MulAction.stabilizer A v := by
    ext a
    change (a.val ∈ A ∧ a.val ∈ Gv (v : G)) ↔ conjugation A V hn a v = v
    rw [and_iff_right a.property]
    rw [Subtype.ext_iff]
    change a.val ∈ centralizer ({(v : G)} : Set G) ↔ _
    rw [mem_centralizer_singleton_iff]
    change a.val * (v : G) = (v : G) * a.val ↔ a.val * (v : G) * a.val⁻¹ = (v : G)
    exact mul_inv_eq_iff_eq_mul.symm
  have hr : (Set.range fun a : f.range => naturalRepresentation (Fin 8) a.val (E (Additive.ofMul v))) =
      (fun u : V => E (Additive.ofMul u)) '' MulAction.orbit A v := by
    ext w
    constructor
    · rintro ⟨⟨_,a,rfl⟩,rfl⟩
      exact ⟨conjugation A V hn a v,⟨a,rfl⟩,hE a (Additive.ofMul v)⟩
    · rintro ⟨u,⟨a,rfl⟩,rfl⟩
      exact ⟨⟨f a,a,rfl⟩,(hE a (Additive.ofMul v)).symm⟩
  rw [Subgroup.relIndex,hs,MulAction.index_stabilizer,hr,
    Nat.card_image_of_injective (f := fun u : V => E (Additive.ofMul u))
      (fun x y h => Additive.ofMul.injective (E.injective h))]
  rfl

/-- Literal pullback of source 12.6.28(1). An elementary actor with no larger
fixed space in corank at most two centralizes the full original V. -/
theorem SourceHypothesis.original_no_three_rigidity
    (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (A : Subgroup G) (hAN : A ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 A]
    (hr : LocalAlternatives.CentralizerRigidity V A 3) : A ≤ centralizer (V : Set G) := by
  obtain ⟨f,_,hf⟩ := S.original_normalizer_permutation_action D hZ hTV
  let E := D.fullLinearCoordinates hZ
  let fA := f.comp (inclusion hAN)
  have he (a : A) (v : Additive V) : E (seedRepresentation A V hAN a v) =
      naturalRepresentation (Fin 8) (fA a) (E v) := hf ⟨a.val,hAN a.property⟩ v.toMul
  let : IsElementaryAbelian 2 fA.range :=
    IsElementaryAbelian.of_surjective fA.rangeRestrict fA.rangeRestrict_surjective
  have hb : fA.range = ⊥ := by
    by_contra hne
    obtain ⟨_,⟨a,rfl⟩,w,hw,hm⟩ := EightRigidity.moved_small_orbit fA.range hne
    obtain ⟨v,hv⟩ := E.surjective w
    let B := A ⊓ Gv (v.toMul : G)
    have hindex : B.relIndex A ≤ 4 := by
      rw [natural_orbit_centralizer_index hAN E fA he v.toMul]
      change Nat.card (Set.range fun a : fA.range => naturalRepresentation (Fin 8) a.val (E v)) ≤ 4
      rw [hv]
      exact hw
    have hc : ChapterE.subgroupCorank A B < 3 :=
      lt_of_le_of_lt (Nat.log_mono_right hindex) (by decide : Nat.log 2 4 < 3)
    have hvB : (v.toMul : G) ∈ V ⊓ centralizer (B : Set G) := by
      refine ⟨v.toMul.property,?_⟩
      intro b hb
      exact mem_centralizer_singleton_iff.mp hb.2
    have hvA : (v.toMul : G) ∈ centralizer (A : Set G) := (hr B inf_le_left hc ▸ hvB).2
    have hfix : conjugation A V hAN a v.toMul = v.toMul := by
      apply Subtype.ext
      change a.val * (v.toMul : G) * a.val⁻¹ = (v.toMul : G)
      rw [hvA a.val a.property,mul_inv_cancel_right]
    apply hm
    rw [←hv,←he]
    exact congrArg E (congrArg Additive.ofMul hfix)
  intro a ha v hv
  have hf1 : fA ⟨a,ha⟩ = 1 := mem_bot.mp (hb ▸ (show fA ⟨a,ha⟩ ∈ fA.range from ⟨⟨a,ha⟩,rfl⟩))
  have hh := he ⟨a,ha⟩ (Additive.ofMul ⟨v,hv⟩)
  rw [hf1,map_one,Module.End.one_apply] at hh
  have heq := congrArg (fun x : Additive V => (x.toMul : G)) (E.injective hh)
  change a * v * a⁻¹ = v at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

variable (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
include hz hTV hTz hbound hTI hns in
/-- The original zeroth weak closure centralizes V, with the intrinsic
corank-three exclusion and its actual permutation marking constructed. -/
theorem SourceHypothesis.original_weakClosure_zero_centralizes :
    ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G) := by
  have hR := (S.fixed_free_intersections_of_control D hTV hTI hZ hns).2
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAW,hindex⟩,hAT⟩
  have hA : A = V.map (MulAut.conj g).toMonoidHom :=
    le_antisymm hAW (relIndex_eq_one.mp (by simpa using hindex))
  let : IsElementaryAbelian 2 A := hA.symm ▸ IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  by_contra hn
  have hi : V ⊓ A = ⊥ := by
    by_contra hi
    have hc := S.original_intersecting_conjugates_commute D hZ z hz hTV hTz hbound hTI hns g
      (hA ▸ hi)
    rw [←hA] at hc
    exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  have hcentral : V ⊓ normalizer (A : Set G) ≤ centralizer (A : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_antisymm _ bot_le
    have hv : ⁅V ⊓ normalizer (A : Set G), A⁆ ≤ V :=
      (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hAT.trans hTV))
    have ha : ⁅V ⊓ normalizer (A : Set G), A⁆ ≤ A :=
      le_normalizer_iff_commutator_le_right.mp inf_le_right
    exact (le_inf hv ha).trans hi.le
  apply hn
  apply S.original_no_three_rigidity D hZ hTV A (hAT.trans hTV)
  intro B hBA hcor
  have hnB : centralizer (B : Set G) ≤ normalizer (A : Set G) := by
    apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR hBA
    have he : ChapterE.globalR A = ChapterE.globalR V := by rw [hA,ChapterE.globalR_map_equiv]
    rw [he]
    exact lt_of_lt_of_le (by exact_mod_cast hcor) hR
  exact le_antisymm
    ((le_inf inf_le_left ((inf_le_right : V ⊓ centralizer (B : Set G) ≤ _).trans hnB)).trans
      (le_inf inf_le_left hcentral))
    (inf_le_inf_left V (Subgroup.centralizer_le hBA))

include hz hTV hTz hbound hTI hns in
/-- The same original zeroth weak closure has its full normalizer in M. -/
theorem SourceHypothesis.original_weakClosure_zero_normalizer_le :
    normalizer (ChapterE.indexedWeakClosure V T 0 : Set G) ≤ M L := by
  have hc := S.original_weakClosure_zero_centralizes D hZ z hz hTV hTz hbound hTI hns
  have hw : 0 < ChapterE.globalW V T := by
    have hle : (1 : ℕ∞) ≤ ChapterE.globalW V T := by
      apply le_iInf
      intro j
      apply le_iInf
      intro hj
      have hj0 : 0 < j := by
        by_contra hn
        have he : j = 0 := by omega
        subst j
        exact hj (le_inf (ChapterE.indexedWeakClosure_le V T 0) hc)
      exact_mod_cast hj0
    exact lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hle
  exact ChapterE.SourceContainment.normalizer_weakClosure_zero_le
    ⟨S.chosen.ne_bot,S.chosen.le_sylow,hTV⟩ hw (by
      have ho : componentOrbit V (T : Subgroup G) = V :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
          (le_componentOrbit V T)
      simpa only [ho,M] using S.chosen.doubledOrbit_centralizer_unique S.source)
end CFSG.Quasithin.Chapter12.Section06
