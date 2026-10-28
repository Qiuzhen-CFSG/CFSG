module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FullFusion
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.WeakClosure
public import Theory.Representation.BinaryPermutation.EightSmallOrbits
/-!
# Weak closure of the original module with nontrivial fixed space

The literal elementary permutation image of a subgroup A of V^g, of
corank at most one, cannot have order at least eight. The intrinsic
small-orbit theorem supplies two original vectors whose centralizers in
A have index at most four. Both vectors therefore belong to the source
centralizer span. Their same-actor commutator product lies in V intersect
V^g and has weight two or eight, contradicting the already proved fusion
and full-centralizer control.

The image thus has binary rank at most two. Its exact action kernel is
C_A(V), so r(G,V)>=4 forces V to normalize V^g. If V^g also lies in T,
mutual normalization and the unrestricted involution-displacement theorem
force centralization. This proves W0 centralizes V; the original Sylow
transport equivalences then give W1<=C_T(V), w(G,V)>1, and the small-corank
normalization assertion with the literal N_G(V).

Every action is restricted from the existing LT permutation action;
the original V, its full fixed line and the given quotient projection
are retained. The source's replacement of N_G(V) by M uses the earlier
12.2.2 normalizer identification. No such identification is inferred here
from TI. The fixed-space elimination in 12.6.23 and the fixed-free HS/J4
branches of 12.6.2 remain with source assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.20--22, printed p.829, and E.3.25,32.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem core_neg (w : core (Fin 8)) : -w = w := by
  apply Subtype.ext
  funext i
  exact CharTwo.neg_eq _

omit [Finite G] in
private theorem restrict_marked_action
    {J A : Subgroup G} (hAJ : A ≤ J) (hJV : J ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (f : J →* Equiv.Perm (Fin 8))
    (hE : ∀ a w, E (seedRepresentation J V hJV a w) =
      coreRepresentation (Fin 8) (f a) (E w)) :
    ∀ a w, E (seedRepresentation A V (hAJ.trans hJV) a w) =
      coreRepresentation (Fin 8) ((f.comp (inclusion hAJ)) a) (E w) := by
  intro a w
  exact hE (inclusion hAJ a) w

omit [Finite G] in
private theorem marked_action_ker
    {A : Subgroup G} (hn : A ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (f : A →* Equiv.Perm (Fin 8))
    (hE : ∀ a w, E (seedRepresentation A V hn a w) =
      coreRepresentation (Fin 8) (f a) (E w)) :
    f.ker = (centralizer (V : Set G)).subgroupOf A := by
  rw [←conjugation_ker A V hn]
  ext a
  change f a = 1 ↔ conjugation A V hn a = 1
  constructor
  · intro ha
    apply MulEquiv.ext
    intro w
    apply Additive.ofMul.injective
    apply E.injective
    have he := hE a (Additive.ofMul w)
    rw [ha,map_one,Module.End.one_apply] at he
    exact he
  · intro ha
    apply FourBlockThompson.coreAut_injective
    apply MulEquiv.ext
    intro w
    obtain ⟨u,hu⟩ := E.surjective w.toAdd
    have he := hE a u
    change E (Additive.ofMul (conjugation A V hn a u.toMul)) = _ at he
    rw [ha] at he
    change E u = coreRepresentation (Fin 8) (f a) (E u) at he
    rw [hu] at he
    exact congrArg Multiplicative.ofAdd he.symm

omit [Finite G] in
private theorem orbit_centralizer_index
    {A : Subgroup G} (hn : A ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (f : A →* Equiv.Perm (Fin 8))
    (hE : ∀ a w, E (seedRepresentation A V hn a w) =
      coreRepresentation (Fin 8) (f a) (E w)) (v : V) :
    (A ⊓ Gv (v : G)).relIndex A =
      Nat.card (Set.range fun a : f.range => coreRepresentation (Fin 8) a.val (E (Additive.ofMul v))) := by
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
  have hr : (Set.range fun a : f.range => coreRepresentation (Fin 8) a.val (E (Additive.ofMul v))) =
      (fun u : V => E (Additive.ofMul u)) '' MulAction.orbit A v := by
    ext w
    constructor
    · rintro ⟨⟨_,a,rfl⟩,rfl⟩
      refine ⟨conjugation A V hn a v,?_,hE a (Additive.ofMul v)⟩
      exact ⟨a,rfl⟩
    · rintro ⟨u,⟨a,rfl⟩,rfl⟩
      exact ⟨⟨f a,a,rfl⟩,(hE a (Additive.ofMul v)).symm⟩
  rw [Subgroup.relIndex,hs,MulAction.index_stabilizer,hr,
    Nat.card_image_of_injective (f := fun u : V => E (Additive.ofMul u))
      (fun x y h => Additive.ofMul.injective (E.injective h))]
  rfl

/-- A small orbit places the original vector in the literal centralizer span.
The corank uses the full conjugate V^g, including its central kernel. -/
private theorem vector_mem_span
    {A : Subgroup G} {g : G} (hA : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hk : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (v : V) (hv : (A ⊓ Gv (v : G)).relIndex A ≤ 4) :
    (v : G) ∈ CentralLine.centralizerSpan V A g := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hcor : ChapterE.subgroupCorank W (A ⊓ Gv (v : G)) ≤ 3 := by
    have hh := ChapterE.offender_corank_add (W := W)
      (show A ⊓ Gv (v : G) ≤ A from inf_le_left) hA
    have hb : ChapterE.subgroupCorank A (A ⊓ Gv (v : G)) ≤ 2 :=
      (Nat.log_mono_right hv).trans (by decide)
    change ChapterE.subgroupCorank W A ≤ 1 at hk
    omega
  apply (show V ⊓ centralizer (A ⊓ Gv (v : G) : Set G) ≤ CentralLine.centralizerSpan V A g from
    le_iSup_of_le (A ⊓ Gv (v : G)) (le_iSup_of_le ⟨inf_le_left,hcor⟩ le_rfl))
  refine ⟨v.property,?_⟩
  intro b hb
  exact mem_centralizer_singleton_iff.mp hb.2

private theorem forbidden_intersection_weight
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {g : G} (hg : g ∉ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (x' : V) (hi : (x' : G) ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hweight : hammingNorm (E (Additive.ofMul x')).val = 2 ∨
      hammingNorm (E (Additive.ofMul x')).val = 8) : False := by
  let x : G := x'
  have hx1 : x ≠ 1 := by
    intro hx1
    have hx0 : Additive.ofMul x' = 0 := congrArg Additive.ofMul (Subtype.ext hx1)
    rw [hx0,E.map_zero] at hweight
    norm_num [hammingNorm] at hweight
  have hcM : Gv x ≤ M L := by
    by_cases hzero : (Submodule.Quotient.mk (Additive.ofMul x') :
        Vhat L V H.chosen.normalizes) = 0
    · exact H.fixed_vector_centralizer_le D hTV x
        ((mem_fixedSeed_iff L V H.chosen.normalizes (Additive.ofMul x')).mp
          ((Submodule.Quotient.mk_eq_zero _).mp hzero)) hx1
    · apply H.nonsingular_centralizer_le_of_fixed D hTV hTI hz x'
      intro hs
      have hq : coreToNatural (Fin 8) (E (Additive.ofMul x')) ≠ 0 := by
        rw [hproj]
        exact fun hh => hzero (D.coordinates.injective (hh.trans D.coordinates.map_zero.symm))
      have hw : hammingNorm (E (Additive.ofMul x')).val = 4 :=
        (EightGeometry.nonzero_singular_core_iff (E (Additive.ofMul x'))).mp
          ⟨hq,by rw [hproj]; exact hs⟩
      omega
  exact hg (mem_normalizer_iff_map_conj_eq.mpr
    (CentralLine.unique_conjugate_of_centralizer_le H.chosen.normalizes
      (H.controls_element_fusion D hTV hTI) hTI hi.1 hx1 hcM hi.2))

/-- The eight-point calculation in 12.6.22 applied to the original module
and actual conjugate. A normalizing intersection of corank at most one
cannot induce an elementary permutation group of order at least eight. -/
theorem SourceHypothesis.small_corank_permutation_image_lt_eight
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {g : G} (hg : g ∉ normalizer (V : Set G))
    {A : Subgroup G} (hA : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hn : A ≤ normalizer (V : Set G))
    (hk : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (f : A →* Equiv.Perm (Fin 8))
    (hE : ∀ a w, E (seedRepresentation A V hn a w) =
      coreRepresentation (Fin 8) (f a) (E w)) : Nat.card f.range < 8 := by
  classical
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hA
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  by_contra! hc
  obtain ⟨a,⟨a,rfl⟩,v,w,hv,hw,hd⟩ := EightSmallOrbits.large_actor_witness f.range hc
  let v' : V := (E.symm v).toMul
  let w' : V := (E.symm w).toMul
  have hv' : E (Additive.ofMul v') = v := E.apply_symm_apply v
  have hw' : E (Additive.ofMul w') = w := E.apply_symm_apply w
  have hvi : (v' : G) ∈ CentralLine.centralizerSpan V A g := by
    apply vector_mem_span hA hk
    rw [orbit_centralizer_index hn E f hE,hv']
    exact hv
  have hwi : (w' : G) ∈ CentralLine.centralizerSpan V A g := by
    apply vector_mem_span hA hk
    rw [orbit_centralizer_index hn E f hE,hw']
    exact hw
  let x : G := ⁅(a : G),(v' : G)⁆ * ⁅(a : G),(w' : G)⁆
  have hx : x ∈ ⁅A,CentralLine.centralizerSpan V A g⁆ :=
    mul_mem (commutator_mem_commutator a.property hvi) (commutator_mem_commutator a.property hwi)
  have hi := CentralLine.commutator_centralizerSpan_le hA hn
    (H.fixed_core_intersections D hTV hTI hz).2 hx
  let x' : V := ⟨x,hi.1⟩
  have hcalc (y : V) :
      E (Additive.ofMul (conjugation A V hn a y * y⁻¹)) =
        coreRepresentation (Fin 8) (f a) (E (Additive.ofMul y)) + E (Additive.ofMul y) := by
    rw [ofMul_mul,map_add,ofMul_inv,map_neg]
    change E (seedRepresentation A V hn a (Additive.ofMul y)) + _ = _
    rw [hE,core_neg]
  have he : E (Additive.ofMul x') =
      coreRepresentation (Fin 8) (f a) v + v + (coreRepresentation (Fin 8) (f a) w + w) := by
    have hx' : x' = (conjugation A V hn a v' * v'⁻¹) *
        (conjugation A V hn a w' * w'⁻¹) := by
      apply Subtype.ext
      rfl
    rw [hx']
    rw [ofMul_mul,map_add,hcalc,hcalc,hv',hw']
  have hweight : hammingNorm (E (Additive.ofMul x')).val = 2 ∨
      hammingNorm (E (Additive.ofMul x')).val = 8 := by rw [he]; exact hd
  exact forbidden_intersection_weight H D hTV hTI hz hg E hproj x' hi hweight

/-- The original Sylow-positioned small-corank intersection is normalized
by V. This uses the full Q-kernel of the literal eight-letter action. -/
theorem SourceHypothesis.small_corank_reverse_normalizes
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {g : G} {A : Subgroup G} (hA : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAT : A ≤ T)
    (hk : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1) :
    V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  classical
  by_cases hg : g ∈ normalizer (V : Set G)
  · have he : V.map (MulAut.conj g).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp hg
    rw [he]
    exact V.le_normalizer
  obtain ⟨E,hEL,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  obtain ⟨f,_,hE,_,_⟩ := H.exists_core_permutation_action D hTV E hEL
  let hn : A ≤ normalizer (V : Set G) := hAT.trans hTV
  let fA : A →* Equiv.Perm (Fin 8) := f.comp (inclusion (hAT.trans (show (T : Subgroup G) ≤ LT T L from le_sup_right)))
  have hEA : ∀ a w, E (seedRepresentation A V hn a w) =
      coreRepresentation (Fin 8) (fA a) (E w) :=
    restrict_marked_action _ _ E f hE
  have hb := H.small_corank_permutation_image_lt_eight D hTV hTI hz hg hA hn hk E hproj fA hEA
  have hker := marked_action_ker hn E fA hEA
  let B := A ⊓ centralizer (V : Set G)
  have hc : B.relIndex A = Nat.card fA.range := by
    rw [←index_ker,hker,Subgroup.relIndex]
    congr 1
    ext a
    exact and_iff_right a.property
  have hlog : ChapterE.subgroupCorank A B ≤ 2 := by
    change Nat.log 2 (B.relIndex A) ≤ 2
    rw [hc]
    exact (Nat.log_mono_right (by omega : Nat.card fA.range ≤ 7)).trans (by decide)
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have hcor : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B ≤ 3 := by
    have hh := ChapterE.offender_corank_add (show B ≤ A from inf_le_left) hA
    omega
  have hr := (H.fixed_core_intersections D hTV hTI hz).2
  have hCN := ChapterE.centralizer_le_normalizer_of_corank_lt_globalR
    ((show B ≤ A from inf_le_left).trans hA)
    (show (ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B : ℕ∞) <
      ChapterE.globalR (V.map (MulAut.conj g).toMonoidHom) by
      rw [ChapterE.globalR_map_equiv]
      exact lt_of_lt_of_le (by exact_mod_cast (show ChapterE.subgroupCorank
        (V.map (MulAut.conj g).toMonoidHom) B < 4 by omega)) hr)
  exact (le_centralizer_iff.mp (show B ≤ centralizer (V : Set G) from inf_le_right)).trans hCN

/-- Two mutually normalizing original conjugates centralize one another
in the nontrivial-fixed-space branch. The full augmentation core is essential. -/
theorem SourceHypothesis.mutual_conjugate_centralizes
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {g : G} (hWT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hVN : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  classical
  by_cases hg : g ∈ normalizer (V : Set G)
  · have he : V.map (MulAut.conj g).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp hg
    rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let hn : W ≤ normalizer (V : Set G) := hWT.trans hTV
  obtain ⟨E,hEL,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  obtain ⟨f,_,hE,_,_⟩ := H.exists_core_permutation_action D hTV E hEL
  let fW : W →* Equiv.Perm (Fin 8) := f.comp (inclusion (hWT.trans (show (T : Subgroup G) ≤ LT T L from le_sup_right)))
  have hEW : ∀ a w, E (seedRepresentation W V hn a w) =
      coreRepresentation (Fin 8) (fW a) (E w) :=
    restrict_marked_action _ _ E f hE
  intro a ha
  let a' : W := ⟨a,ha⟩
  have heq : fW a' = 1 := by
    by_contra hne
    have hp : (fW a')^2 = 1 := by
      rw [←map_pow,show a'^2=1 from Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ ha),map_one]
    obtain ⟨v,hv⟩ := EightSmallOrbits.involution_displacement (fW a') hp hne
    let v' : V := (E.symm v).toMul
    let x : G := ⁅a,(v' : G)⁆
    have hx : x ∈ ⁅W,V⁆ := commutator_mem_commutator ha v'.property
    have hi : x ∈ V ⊓ W := ⟨(le_normalizer_iff_commutator_le_right.mp hn) hx,
      (le_normalizer_iff_commutator_le_left.mp hVN) hx⟩
    let x' : V := ⟨x,hi.1⟩
    have he : E (Additive.ofMul x') = coreRepresentation (Fin 8) (fW a') v + v := by
      have hx' : x' = conjugation W V hn a' v' * v'⁻¹ := by apply Subtype.ext; rfl
      rw [hx']
      rw [ofMul_mul,map_add,ofMul_inv,map_neg]
      change E (seedRepresentation W V hn a' (Additive.ofMul v')) + _ = _
      rw [hEW,show E (Additive.ofMul v') = v from E.apply_symm_apply v,core_neg]
    exact forbidden_intersection_weight H D hTV hTI hz hg E hproj x' hi (by rw [he]; exact hv)
  intro v hv
  have he := hEW a' (Additive.ofMul ⟨v,hv⟩)
  rw [heq,map_one,Module.End.one_apply] at he
  have he' := congrArg (fun w : Additive V => (w.toMul : G)) (E.injective he)
  change a * v * a⁻¹ = v at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- Source 12.6.22(1): the original zeroth weak closure centralizes V. -/
theorem SourceHypothesis.fixed_weakClosure_zero_centralizes
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G) := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAW,hindex⟩,hAT⟩
  have he : A = V.map (MulAut.conj g).toMonoidHom :=
    le_antisymm hAW (relIndex_eq_one.mp (by simpa using hindex))
  subst A
  apply H.mutual_conjugate_centralizes D hTV hTI hz hAT
  apply H.small_corank_reverse_normalizes D hTV hTI hz le_rfl hAT
  simp [ChapterE.subgroupCorank]

/-- All corank-zero and corank-one weak-closure generators centralize V,
using the actual conjugate and the original selected Sylow subgroup. -/
theorem SourceHypothesis.fixed_weakClosure_one_centralizes
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {i : ℕ} (hi : i ≤ 1) :
    ChapterE.indexedWeakClosure V T i ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  apply le_inf (ChapterE.indexedWeakClosure_le V T i)
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAW,hindex⟩,hAT⟩
  have hk : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1 := by
    unfold ChapterE.subgroupCorank
    rw [hindex,Nat.log_pow (by decide)]
    exact hi
  have hn := H.small_corank_reverse_normalizes D hTV hTI hz hAW hAT hk
  have hc := (ChapterE.conjugate_normalization_equivalences_of_weakClosure_zero hTV
    (H.fixed_weakClosure_zero_centralizes D hTV hTI hz) g).2.2.mpr hn
  exact hAW.trans (le_centralizer_iff.mp hc)

/-- Source 12.6.22(3), without a weak-closure or permutation hypothesis. -/
theorem SourceHypothesis.fixed_globalW_gt_one
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    1 < ChapterE.globalW V T := by
  have htwo : 2 ≤ ChapterE.globalW V T := by
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    have hb : 2 ≤ i := by
      by_contra! hn
      exact hi (H.fixed_weakClosure_one_centralizes D hTV hTI hz (by omega))
    exact_mod_cast hb
  exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) htwo

/-- The small-corank normalizer assertion, with the literal N_G(V) used
by the weak-closure parameters. Source 12.2.2 identifies it with M in this
fixed-space branch; that earlier normalizer identification is kept separate. -/
theorem SourceHypothesis.fixed_small_corank_normalizes
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (g : G)
    (hk : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (ChapterE.offenderNormalizer V g) ≤ 1) :
    V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := ChapterE.offenderNormalizer V g
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let k := ChapterE.subgroupCorank W A
  have hi : A.relIndex W = 2^k := by
    change A.relIndex W = 2 ^ ChapterE.subgroupCorank W A
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank W A
  have hAC := ChapterE.conjugateCorankFamily_le_centralizer_of_weakClosure V T hTV
    (show A ∈ ChapterE.conjugateCorankFamily V k from ⟨g,inf_le_left,hi⟩)
    (IsElementaryAbelian.isPGroup 2 A) inf_le_right
    ((H.fixed_weakClosure_one_centralizes D hTV hTI hz hk).trans inf_le_right)
  have hr := (H.fixed_core_intersections D hTV hTI hz).2
  change ChapterE.subgroupCorank W A ≤ 1 at hk
  have hCN := ChapterE.centralizer_le_normalizer_of_corank_lt_globalR
    (show A ≤ W from inf_le_left)
    (show (ChapterE.subgroupCorank W A : ℕ∞) < ChapterE.globalR W by
      rw [ChapterE.globalR_map_equiv]
      exact lt_of_lt_of_le (by exact_mod_cast (show ChapterE.subgroupCorank W A < 4 by omega)) hr)
  have hVN : V ≤ normalizer (W : Set G) := (le_centralizer_iff.mp hAC).trans hCN
  have he := ChapterE.conjugate_normalization_equivalences_of_weakClosure_zero hTV
    (H.fixed_weakClosure_zero_centralizes D hTV hTI hz) g
  exact he.1.mpr (he.2.1.mpr (he.2.2.mpr hVN))

end CFSG.Quasithin.Chapter12.Section06
