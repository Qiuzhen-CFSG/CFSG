module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaModule
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiPairGeneration
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiOddFixedSpaces

/-!
# The large-unitary reduction in DGS 8.3

A quadratic pair generating the quotient decomposes its whole commutator
space. With zero global fixed space, the commutator of one actor is already
contained in that of any involution which generates with the other actor.
Suzuki pair generation applies this to the entire Sylow omega-center and
any of its nonidentity elements. Cyclic Sylows handle Sz(2); two-rank one
handles SU₃(2), PSU₃(2), and D₁₀, retaining the special unitary scalar center.

Identity coordinates on the original moving center transport this inclusion
through the specified local quotient. The existing linear case then completes
the source catalogue reduction: a counterexample to 8.3 must have an actual
large unitary quotient. The corrected generation and residual-fixed premises
on the original center are supplied by the existing source preparation.
No reverse-containment, natural-module, or whole-action-faithfulness premise
is added. `OmegaCommutatorApplication` constructs the literal reduced-source
moving neighbor and its full-edge Sylow.

Source: DGS, *Groups and Graphs* (1985), (8.3)(1), printed p.135, using
(8.1)(h), (5.2), (5.3), and the quadratic-pair argument of (5.8)(d).
The large unitary contradiction and the later Chapter 8 conclusions remain
separate obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

private theorem moved_cyclic_of_quadratic_pair {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A B : Subgroup D) (t : D) (ht : t ∈ A)
    (hA : IsQuadratic ρ A) (hB : IsQuadratic ρ B)
    (hgen : zpowers t ⊔ B = ⊤) (hf : fixedSpace ρ ⊤ = ⊥) :
    Coinvariants.ker (ρ.comp A.subtype) ≤ Coinvariants.ker (ρ.comp (zpowers t).subtype) := by
  have htA : zpowers t ≤ A := zpowers_le.mpr ht
  have hmA : Coinvariants.ker (ρ.comp A.subtype) ≤ fixedSpace ρ A :=
    (commutator_le_invariants_iff _).mpr (fun a b v => hA a a.property b b.property v)
  have hmt : Coinvariants.ker (ρ.comp (zpowers t).subtype) ≤ fixedSpace ρ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩ b
    exact hA b b.property a (htA a.property) v
  have hmB : Coinvariants.ker (ρ.comp B.subtype) ≤ fixedSpace ρ B :=
    (commutator_le_invariants_iff _).mpr (fun a b v => hB a a.property b b.property v)
  have hd : Disjoint (fixedSpace ρ (zpowers t)) (fixedSpace ρ B) := by
    apply disjoint_iff.mpr
    rw [←show fixedSpace ρ (zpowers t ⊔ B) = fixedSpace ρ (zpowers t) ⊓ fixedSpace ρ B from
      ρ.invariants_comp_sup _ _,hgen,hf]
  have hm : Coinvariants.ker (ρ.comp A.subtype) ≤ Coinvariants.ker ρ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ) a v
  intro v hv
  have hv' := hm hv
  rw [moved_eq_sup_of_generates ρ (zpowers t) B hgen] at hv'
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv'
  have hyT : y ∈ fixedSpace ρ (zpowers t) := by
    have hyA := (fixedSpace ρ A).sub_mem (hmA hv) (hmt hx)
    exact fixedSpace_antitone ρ htA (by simpa only [add_sub_cancel_left] using hyA)
  have hy0 : y = 0 := hd.le_bot ⟨hyT,hmB hy⟩
  simpa only [hy0,add_zero] using hx

private theorem suzuki_moved_le_cyclic {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {m : ℕ} (hm : 0 < m) (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) W)
    (S : Sylow 2 (SuzukiMatrixGroup m))
    (hq : IsQuadratic ρ (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))))
    (hf : fixedSpace ρ ⊤ = ⊥)
    (t : SuzukiMatrixGroup m) (ht : t ∈ omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m)))
    (ht1 : t ≠ 1) :
    Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))).subtype) ≤
      Coinvariants.ker (ρ.comp (zpowers t).subtype) := by
  have he : omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m)) =
      omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m)) := by
    rw [omegaCenterIn_eq_omegaOneAmbient,suzuki_omega_center_eq]
  let : IsElementaryAbelian 2 (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))) :=
    he.symm ▸ suzukiSylow_omega_elementary hm (MulEquiv.refl _) S
  have hc : 4 ≤ Nat.card (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))) := by
    rw [he,suzukiSylow_omega_card hm (MulEquiv.refl _) S]
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨g,hg⟩ := suzuki_exists_quadratic_pair hm _ hc t ht ht1
  exact moved_cyclic_of_quadratic_pair ρ _ _ t ht hq
    (SL2SylowFixedRecognition.quadratic_conjugate ρ hq g) hg hf

private theorem moved_mono {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {A B : Subgroup D} (hAB : A ≤ B) :
    Coinvariants.ker (ρ.comp A.subtype) ≤ Coinvariants.ker (ρ.comp B.subtype) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,v⟩,rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp B.subtype) ⟨a,hAB a.property⟩ v

private theorem omega_moved_le_of_unique_involution {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (S : Sylow 2 D) (A : Subgroup D)
    (hA : A ≤ omegaCenterIn (S : Subgroup D)) (hne : A ≠ ⊥)
    (hu : ∀ x ∈ omegaCenterIn (S : Subgroup D), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup D), y ≠ 1 → x = y) :
    Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup D)).subtype) ≤
      Coinvariants.ker (ρ.comp A.subtype) := by
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  apply moved_mono ρ
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ A.one_mem
  · exact hu t (hA ht) ht1 y hy hy1 ▸ ht

private theorem center_commutator_le_of_moved_le {D : Type*} [Group D]
    (L Z A Y H : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZL : Z ≤ L) (hnZ : L ≤ normalizer (Z : Set G)) (hYL : Y ≤ L)
    (q : L →* D) (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (z : Additive Z),
      ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹)
    (hm : Coinvariants.ker (ρ.comp ((Y.subgroupOf L).map q).subtype) ≤
      Coinvariants.ker (ρ.comp ((A.subgroupOf L).map q).subtype))
    (hH : ⁅A,Z⁆ ≤ H) : ⁅Y,Z⁆ ≤ H := by
  let δ := centerSection L Z hZL hnZ q ρ hact
  have hA : Coinvariants.ker (ρ.comp ((A.subgroupOf L).map q).subtype) ≤ δ.imageSpace H := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨t,v⟩,rfl⟩
    obtain ⟨a,ha,he⟩ := t.property
    change ρ t.val v - v ∈ δ.imageSpace H
    rw [←he]
    exact δ.displacement_range_le_imageSpace_of_commutator_le A H hH a ha ⟨v,rfl⟩
  apply commutator_le.mpr
  intro y hy z hz
  let l : L := ⟨y,hYL hy⟩
  let v : Additive Z := Additive.ofMul ⟨z,hz⟩
  have hmem : ρ (q l) v - v ∈ δ.imageSpace H :=
    hA (hm (Coinvariants.sub_mem_ker
      (ρ := ρ.comp ((Y.subgroupOf L).map q).subtype)
      ⟨q l,mem_map_of_mem q hy⟩ v))
  obtain ⟨x,hx,hxe⟩ := (δ.mem_imageSpace_iff H _).mp hmem
  have hval := congrArg (fun w : Additive Z => (w.toMul : G)) hxe
  simp only [δ,centerSection,toMul_sub,div_eq_mul_inv] at hval
  change (x : G) = ((ρ (q l) v).toMul : G) * z⁻¹ at hval
  rw [hact] at hval
  change (x : G) = ⁅y,z⁆ at hval
  exact hval ▸ hx

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_omega_commutator_of_moved_control (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hcontrol : letI := CommutingOneProfile.source_center_elementary h w.val
      ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) w.val)))
        (S : Sylow 2 D) (A : Subgroup D),
        IsQuadratic ρ (omegaCenterIn (S : Subgroup D)) → fixedSpace ρ ⊤ = ⊥ →
        A ≤ omegaCenterIn (S : Subgroup D) → A ≠ ⊥ →
        Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup D)).subtype) ≤
          Coinvariants.ker (ρ.comp A.subtype)) :
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let F := family P
  let L := d.localGroup w.val
  let A := V F beta 1 ⊓ Q F a'
  let Y := quotientSylowOmegaPreimage L R
  let q₀ := QuotientGroup.mk' (pCore 2 L)
  let q := e.toMonoidHom.comp q₀
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let S := R.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hz,hAL,_,hAQ,T,_⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
  obtain ⟨ρ,hact⟩ := source_exists_center_quotient_action h d w.val e
  obtain ⟨_,_,_,hres⟩ := source_center_module_prepared_of_center_eq_bot h d w.val hz T e ρ hact
  have hZL : Z F w.val ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  have hYL : Y ≤ L := map_subtype_le _
  let δ := centerSection L (Z F w.val) hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) q ρ hact
  have hYS : (Y.subgroupOf L).map q = omegaCenterIn (S : Subgroup D) := by
    rw [←map_map,show (Y.subgroupOf L).map q₀ = omegaCenterIn ((R : Subgroup L).map q₀) from
      quotientSylowOmegaPreimage_image L R,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,map_map]
    rfl
  have hquad : IsQuadratic ρ (omegaCenterIn (S : Subgroup D)) := by
    rw [←hYS]
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le L (Z F w.val) ⊥ Y ρ q δ
    have he := (source_critical_quotient_omega_action h hB d hc hab hd hb hcomm models w hm R hR).2
    rw [commutator_comm Y,commutator_comm Y]
    exact he.le
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact inf_le_right.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property)
  have hAS : (A.subgroupOf L).map q ≤ S := by
    apply map_mono
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y = x) ▸ hy
  obtain ⟨_,hb3,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hAO : (A.subgroupOf L).map q ≤ omegaCenterIn (S : Subgroup D) :=
    source_rank_one_elementary_le_sylow_omega
      ((models w.val).of_equiv e.symm) S _ hAS
  have hne : (A.subgroupOf L).map q ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [local_quotient_kernel F d w.val e] at hk
    exact hAQ (fun a ha => hk (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))
  apply center_commutator_le_of_moved_le L (Z F w.val) A Y _ hZL δ.normalized hYL q ρ hact
  · rw [hYS]
    exact hcontrol ρ S _ hquad (bot_unique ((fixedSpace_antitone ρ le_top).trans hres.le)) hAO hne
  · exact commutator_mono le_rfl (Z_neighbor_le_V F w.property)

private theorem omega_unique_of_cyclic {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) [IsCyclic S] :
    ∀ x ∈ omegaCenterIn (S : Subgroup D), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup D), y ≠ 1 → x = y := by
  intro x hx hx1 y hy hy1
  have hi (z : D) (hz : z ∈ omegaCenterIn (S : Subgroup D)) (hz1 : z ≠ 1) :
      orderOf (⟨z,((mem_omegaCenterIn_iff _ _).mp hz).1⟩ : S) = 2 :=
    orderOf_eq_prime (Subtype.ext ((mem_omegaCenterIn_iff _ _).mp hz).2.2)
      (fun he => hz1 (congrArg Subtype.val he))
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two (hi x hx hx1) (hi y hy hy1))

private theorem omega_unique_of_rank_one {D : Type*} [Group D] [Finite D]
    (hr : primeRank 2 D ≤ 1) (S : Sylow 2 D) :
    ∀ x ∈ omegaCenterIn (S : Subgroup D), x ≠ 1 →
      ∀ y ∈ omegaCenterIn (S : Subgroup D), y ≠ 1 → x = y := by
  intro x hx hx1 y hy hy1
  exact commuting_involutions_eq_of_two_rank_one hr
    ⟨hx1,((mem_omegaCenterIn_iff _ _).mp hx).2.2⟩
    ⟨hy1,((mem_omegaCenterIn_iff _ _).mp hy).2.2⟩
    (show Commute x y from ((mem_omegaCenterIn_iff _ _).mp hx).2.1 y
      ((mem_omegaCenterIn_iff _ _).mp hy).1 |>.symm)

/-- The exact DGS 8.3 inclusion for every Suzuki parameter, including Sz(2).
The whole original quotient omega-preimage is retained. -/
theorem source_moving_suzuki_quotient_omega_commutator_le (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (m : ℕ) (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* SuzukiMatrixGroup m)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ := by
  apply source_omega_commutator_of_moved_control h hB d hc hab hd hb hcomm models w hm e R hR
  let := CommutingOneProfile.source_center_elementary h w.val
  intro ρ S A hq hf hAO hne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · let T : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
      rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
      rw [show (20 : ℕ) = 2^2 * 5 from rfl,
        Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
      norm_num [Nat.Prime.factorization Nat.prime_two,
        Nat.Prime.factorization (by decide : Nat.Prime 5)])
    let : IsCyclic T := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
    let : IsCyclic S := (Sylow.equiv T S).isCyclic.mp inferInstance
    exact omega_moved_le_of_unique_involution ρ S A hAO hne (omega_unique_of_cyclic S)
  · obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hne
    exact (suzuki_moved_le_cyclic hm ρ S hq hf t (hAO ht) ht1).trans
      (moved_mono ρ (zpowers_le.mpr ht))

/-- In two-rank one, the nonzero original actor fills the quotient
omega-center. This includes both unitary field-two models without
discarding the special unitary scalar center. -/
theorem source_moving_rank_one_quotient_omega_commutator_le (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hr : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ 1)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ := by
  let := finite_endpoints h
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  apply source_omega_commutator_of_moved_control h hB d hc hab hd hb hcomm models w hm
    (MulEquiv.refl _) R hR
  let := CommutingOneProfile.source_center_elementary h w.val
  intro ρ S A _ _ hAO hne
  exact omega_moved_le_of_unique_involution ρ S A hAO hne (omega_unique_of_rank_one hr S)

private def linear_field_lift (K : Type) [Field K] : SL(2,K) ≃* SL(2,ULift.{u} K) where
  toFun := Matrix.SpecialLinearGroup.map ULift.ringEquiv.symm.toRingHom
  invFun := Matrix.SpecialLinearGroup.map ULift.ringEquiv.toRingHom
  left_inv x := by ext i j; rfl
  right_inv x := by ext i j; rfl
  map_mul' x y := (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (ULift.ringEquiv.symm : K ≃+* ULift.{u} K).toRingHom).map_mul x y

/-- A counterexample to DGS 8.3 has an actual large unitary quotient.
All binary linear, Suzuki, D₁₀ and field-two unitary cases satisfy the
original omega-preimage commutator inclusion. -/
theorem source_moving_omega_commutator_or_large_unitary (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
        ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ∨
      ∃ n : ℕ, 2 ≤ n ∧
        (ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
          IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n)) := by
  let := finite_endpoints h
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  cases models w.val with
  | linear n hn hi =>
    left
    obtain ⟨K,_,_,hK,⟨e⟩⟩ := hi
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hK)
    let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact source_moving_linear_quotient_omega_commutator_le h hB d hc hab hd hb hcomm
      models w hm (f.trans (linear_field_lift K)) R hR
  | suzuki m hi =>
    exact Or.inl (source_moving_suzuki_quotient_omega_commutator_le h hB d hc hab hd hb hcomm
      models w hm m hi.some R hR)
  | projective_unitary n hn hi =>
    by_cases hn2 : 2 ≤ n
    · exact Or.inr ⟨n,hn2,Or.inl hi⟩
    left
    have hn1 : n = 1 := by omega
    obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply source_moving_rank_one_quotient_omega_commutator_le h hB d hc hab hd hb hcomm
      models w hm _ R hR
    rw [primeRank_congr 2 e]
    simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
  | special_unitary n hn hi =>
    by_cases hn2 : 2 ≤ n
    · exact Or.inr ⟨n,hn2,Or.inr hi⟩
    left
    have hn1 : n = 1 := by omega
    obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hi
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply source_moving_rank_one_quotient_omega_commutator_le h hB d hc hab hd hb hcomm
      models w hm _ R hR
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    simpa only [hn1] using (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
  | dihedral hi =>
    left
    let e := hi.some
    apply source_moving_rank_one_quotient_omega_commutator_le h hB d hc hab hd hb hcomm
      models w hm _ R hR
    let S := R.mapSurjective (f := QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
      (QuotientGroup.mk'_surjective _)
    have hS : Nat.card S = 2 := by
      rw [S.card_eq_multiplicity,Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
      rw [Nat.factorization_mul (by decide) (by decide),
        Nat.prime_two.factorization,Nat.prime_five.factorization]
      norm_num
    exact S.primeRank_le_one_of_isCyclic (isCyclic_of_prime_card hS)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
