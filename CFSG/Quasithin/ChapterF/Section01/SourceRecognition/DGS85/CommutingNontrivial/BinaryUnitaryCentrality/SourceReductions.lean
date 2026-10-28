module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CoreProductComparison
public import Theory.GroupTheory.Commutator.FixedSeedKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NoncentralPairedComparison

/-!
# Exact binary unitary actors in the commuting critical configuration

For a moving SU₃(2) or PSU₃(2) neighbor, the elementary actor
A = V_beta ∩ Q_alpha' has nonzero image in the quotient Sylow omega-center.
The actual unitary coordinates give that center order two and index four.
Consequently the image is the entire omega-center, its preimage is A Q_w,
and its commutator and fixed subgroup on Z_w agree with those of A.
All equalities retain the original quotient and subgroup embeddings.

The reverse core-product identity bounds the fixed index of Z_alpha on
V_alpha' by twice the opposite core index. The source field-square bounds
then exclude large unitary and positive-parameter Suzuki terminal quotients.
These are reductions of the binary moving branch of 8.7; centrality for
linear and small terminal quotients remains to be established.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
5.10, 8.1 and 8.7, printed pp.111--112,132--140. The binary unitary Sylow
calculation is transported from `HermitianForm.SylowOmegaIndex`, retaining
both the special and projective carriers and their scalar-kernel convention.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

private theorem binary_omega_data {D : Type*} [Group D] [Finite D]
    (hu : ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) (S : Sylow 2 D) :
    Nat.card (omegaCenterIn (S : Subgroup D)) = 2 ∧
      (omegaCenterIn (S : Subgroup D)).relIndex S = 4 := by
  have transport {E : Type} [Group E] (e : D ≃* E) :
      let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
      Nat.card (omegaCenterIn (T : Subgroup E)) = Nat.card (omegaCenterIn (S : Subgroup D)) ∧
        (omegaCenterIn (T : Subgroup E)).relIndex T =
          (omegaCenterIn (S : Subgroup D)).relIndex S := by
    change Nat.card (omegaCenterIn ((S : Subgroup D).map e.toMonoidHom)) = _ ∧
      (omegaCenterIn ((S : Subgroup D).map e.toMonoidHom)).relIndex
        ((S : Subgroup D).map e.toMonoidHom) = _
    rw [←NilesRankOneKernel.omegaCenterIn_map_injective _ e.injective,
      card_map_of_injective e.injective,relIndex_map_map_of_injective _ _ e.injective]
    exact ⟨rfl,rfl⟩
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    have hc := HermitianForm.SylowOmegaIndex.projective J (n := 1) (by decide)
      (by simpa using hK) (by simpa using hconj)
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    exact ⟨(transport e).1.symm.trans (by simpa using hc.1),
      (transport e).2.symm.trans (by simpa using hc.2)⟩
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    have hc := HermitianForm.SylowOmegaIndex.special J (n := 1) (by decide)
      (by simpa using hK) (by simpa using hconj)
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    exact ⟨(transport e).1.symm.trans (by simpa using hc.1),
      (transport e).2.symm.trans (by simpa using hc.2)⟩

variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily J S₀

/-- The actual moving actor fills the binary quotient omega-center. Its
core index is two, and adjoining the neighbor core gives the full omega
preimage, of index four in the original edge Sylow. -/
theorem reduced_moving_actor_eq_omega
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    (R : Sylow 2 (graphLocalGroup Γ w.val))
    (hR : (R : Subgroup (graphLocalGroup Γ w.val)).map
      (graphLocalGroup Γ w.val).subtype =
        (stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2) :
    let L := graphLocalGroup Γ w.val
    let q := QuotientGroup.mk' (pCore 2 L)
    let A := V Γ beta 1 ⊓ Q Γ a'
    (A.subgroupOf L).map q = omegaCenterIn ((R : Subgroup L).map q) ∧
      (Q Γ w.val).relIndex A = 2 ∧
      quotientSylowOmegaPreimage L R = A ⊔ Q Γ w.val ∧
      (A ⊔ Q Γ w.val).relIndex
        ((stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2) = 4 := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let L := graphLocalGroup Γ w.val
  let A := V Γ beta 1 ⊓ Q Γ a'
  let q := QuotientGroup.mk' (pCore 2 L)
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let S := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hb3 : 3 ≤ b Γ := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V Γ beta 1) := CommutingThreeProfile.V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAL : A ≤ L := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.1
  have hAQ : ¬ A ≤ Q Γ w.val := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.2.2.1
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    apply inf_le_right.trans
    rw [inf_comm]
    exact Noncommuting.graph_Q_le_edgeCore ht w.property
  have hAS : (A.subgroupOf L).map q ≤ S := by
    apply map_mono
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hAO := source_rank_one_elementary_le_sylow_omega (models w.val) S _ hAS
  have hAn : (A.subgroupOf L).map q ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [show q.ker = (Q Γ w.val).subgroupOf L from
      local_quotient_kernel Γ d w.val (MulEquiv.refl _)] at hk
    exact hAQ (fun x hx => hk (show (⟨x,hAL hx⟩ : L) ∈ A.subgroupOf L from hx))
  obtain ⟨hcard,hindex⟩ := binary_omega_data hu S
  have heq : (A.subgroupOf L).map q = omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L)) := by
    apply eq_of_le_of_card_ge hAO
    rw [hcard]
    exact ((A.subgroupOf L).map q).one_lt_card_iff_ne_bot.mpr hAn
  have hi := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex L
    (Q Γ w.val) A q (local_quotient_kernel Γ d w.val (MulEquiv.refl _)) hAL
  have hpre := congrArg (fun U : Subgroup (L ⧸ pCore 2 L) => (U.comap q).map L.subtype) heq
  rw [comap_map_eq,Subgroup.map_sup,map_subgroupOf_eq_of_le hAL,QuotientGroup.ker_mk'] at hpre
  change A ⊔ L.pCoreIn 2 = quotientSylowOmegaPreimage L R at hpre
  rw [show L.pCoreIn 2 = Q Γ w.val from localGroup_core_eq Γ d w.val] at hpre
  refine ⟨heq,hi.symm.trans ((congrArg (fun U : Subgroup (L ⧸ pCore 2 L) => Nat.card U) heq).trans hcard),
    hpre.symm,?_⟩
  rw [hpre,←hR]
  unfold quotientSylowOmegaPreimage
  rw [relIndex_map_map_of_injective _ _ L.subtype_injective,relIndex_comap]
  exact hindex

/-- Equality of the literal actor images gives equality of both the
commutator and the fixed subgroup on the unchanged neighboring center. -/
theorem reduced_moving_root_action
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    (R : Sylow 2 (graphLocalGroup Γ w.val))
    (hR : (R : Subgroup (graphLocalGroup Γ w.val)).map
      (graphLocalGroup Γ w.val).subtype =
        (stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2) :
    let A := V Γ beta 1 ⊓ Q Γ a'
    let Y := quotientSylowOmegaPreimage (graphLocalGroup Γ w.val) R
    ⁅Y,Z Γ w.val⁆ = ⁅A,Z Γ w.val⁆ ∧
      Z Γ w.val ⊓ centralizer (Y : Set (Reduction.G₀ J S₀)) =
        Z Γ w.val ⊓ centralizer (A : Set (Reduction.G₀ J S₀)) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let L := graphLocalGroup Γ w.val
  let A := V Γ beta 1 ⊓ Q Γ a'
  let Y := quotientSylowOmegaPreimage L R
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨heq,_,hpre,_⟩ := reduced_moving_actor_eq_omega h models hc hab hd hb hcomm w hm hu R hR
  change Y = A ⊔ Q Γ w.val at hpre
  have hAL : A ≤ L := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.1
  have hYL : Y ≤ L := map_subtype_le _
  have hZL : Z Γ w.val ≤ L := by
    let : IsElementaryAbelian 2 (Z Γ w.val) := CommutingOneProfile.source_center_elementary ht w.val
    exact pGroup_le_localGroup Γ d w.val _ (IsElementaryAbelian.isPGroup 2 _)
      (Z_le_stabilizer Γ w.val)
  have hZQ := Z_centralizes_Q Γ w.val (source_Z_Q_U ht w.val).1
  have hker : q.ker ≤ centralizer ((Z Γ w.val).subgroupOf L : Set L) := by
    rw [show q.ker = (Q Γ w.val).subgroupOf L from
      local_quotient_kernel Γ d w.val (MulEquiv.refl _)]
    intro x hx z hz
    exact Subtype.ext ((le_centralizer_iff.mp hZQ) hx z.val hz)
  have he := commutator_eq_of_centralizing_kernel (G := L)
    ((Z Γ w.val).subgroupOf L) ((Z Γ w.val).subgroupOf L)
    (Y.subgroupOf L) (A.subgroupOf L) q hker le_rfl
    ((quotientSylowOmegaPreimage_image L R).trans heq.symm)
  have he' := congrArg (fun U : Subgroup L => U.map L.subtype) he
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hZL,
    map_subgroupOf_eq_of_le hAL,map_subgroupOf_eq_of_le hYL,
    commutator_comm (Z Γ w.val) Y,commutator_comm (Z Γ w.val) A] at he'
  refine ⟨he',?_⟩
  have hAY : A ≤ Y := hpre.symm ▸ le_sup_left
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hAY))
  apply le_inf inf_le_left
  apply le_centralizer_iff.mp
  rw [hpre]
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (le_centralizer_iff.mp (inf_le_left.trans hZQ))

private theorem binary_rank {D : Type*} [Group D] [Finite D]
    (hu : ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) : primeRank 2 D ≤ 1 := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le

private theorem binary_not_dihedral {D : Type*} [Group D] [Finite D]
    (hu : ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) : ¬ Nonempty (D ≃* DihedralGroup 5) := by
  rintro ⟨e⟩
  let S : Sylow 2 D := default
  obtain ⟨hcard,hindex⟩ := binary_omega_data hu S
  have hmul := ((omegaCenterIn (S : Subgroup D)).subgroupOf S).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (map_subtype_le _)).toEquiv] at hmul
  change Nat.card (omegaCenterIn (S : Subgroup D)) *
    (omegaCenterIn (S : Subgroup D)).relIndex S = Nat.card S at hmul
  rw [hcard,hindex] at hmul
  have horder := (S : Subgroup D).card_mul_index
  rw [←hmul,Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at horder
  omega

private theorem unitary_omega_card {D : Type*} [Group D] [Finite D]
    {k : ℕ} (hk : 0 < k)
    (hu : ClassicalGroup.IsPSU D 3 (2^k) ∨ IsSU D 3 (2^k)) (S : Sylow 2 D) :
    Nat.card (omegaCenterIn (S : Subgroup D)) = 2^k := by
  have transport {E : Type} [Group E] (e : D ≃* E) :
      Nat.card (omegaCenterIn ((S.mapSurjective (f := e.toMonoidHom) e.surjective :
        Sylow 2 E) : Subgroup E)) = Nat.card (omegaCenterIn (S : Subgroup D)) := by
    change Nat.card (omegaCenterIn ((S : Subgroup D).map e.toMonoidHom)) = _
    rw [←NilesRankOneKernel.omegaCenterIn_map_injective _ e.injective,
      card_map_of_injective e.injective]
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact (transport e).symm.trans ((HermitianForm.SylowOmegaIndex.projective J hk hK hconj
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)).1)
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact (transport e).symm.trans ((HermitianForm.SylowOmegaIndex.special J hk hK hconj
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)).1)

/-- The reversed core-product comparison on the source graph. The binary
moving marking bounds the secondary actor index by two; no fixed-subgroup
escape or centrality assumption is used. -/
theorem reduced_terminal_fixed_index_le_twice
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : (centralizer (Z Γ a : Set (Reduction.G₀ J S₀))).relIndex (V Γ a' 1) ≤
      (Q Γ beta).relIndex (V Γ a' 1) * 2 := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (graphLocalGroup Γ w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hrw : primeRank 2 (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) ≤ 1 :=
    binary_rank hu
  have hVP : V Γ a' 1 ≤ stabilizer Γ a' := V_le_stabilizer_of_dist_add_le_b Γ ht.generate
    a' a' 1 (by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V Γ a' 1) := Finite.of_injective (inclusion hVP) (inclusion_injective _)
  have hup := relIndex_le_of_le_left
    (le_centralizer_iff.mp (Z_centralizes_Q Γ a (source_Z_Q_U ht a).1))
    (((Q Γ a).subgroupOf (V Γ a' 1)).index_ne_zero_of_finite)
  have hpair := source_paired_core_indices ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm 1 hrw
  have hprod := hpair.2.1
  have htwo := hpair.2.2.2
  simp only [pow_one] at htwo
  change (Q Γ beta).relIndex (V Γ a' 1) *
    (Q Γ a).relIndex (V Γ a' 1 ⊓ Q Γ beta) = (Q Γ a).relIndex (V Γ a' 1) at hprod
  exact hup.trans (hprod.symm.le.trans (Nat.mul_le_mul_left _ htwo))

/-- A binary moving neighbor excludes either large unitary cover at the
terminal vertex. The original movement supplies the nonzero H required by
the distance-three and opposite-omega arguments. -/
theorem reduced_large_unitary_terminal_impossible
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    {k : ℕ} (hk : 2 ≤ k)
    (htm : ClassicalGroup.IsPSU (graphLocalGroup Γ a' ⧸
      pCore 2 (graphLocalGroup Γ a')) 3 (2^k) ∨
      IsSU (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) 3 (2^k)) : False := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : ∀ v, Finite (graphLocalGroup Γ v) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans hz.le))
  have htype : a.type = w.val.type := by
    have hodd := (source_critical_geometry ht d hc hab hd hb hcomm).1
    have hna : a.type ≠ a'.type := by
      intro he
      have heven := (even_dist_iff Γ ht.generate a a').mpr he
      rw [hc.1] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    exact (Bool.eq_not_of_ne hna).trans (Bool.eq_not_of_ne w.property.1.symm).symm
  have hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5) := by
    obtain ⟨g,hg⟩ := (same_orbit_iff Γ a w.val).mpr htype
    obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport ht g hg
    rintro ⟨e⟩
    exact binary_not_dihedral hu ⟨f.symm.trans e⟩
  let R : Sylow 2 (graphLocalGroup Γ beta) := default
  let T : Sylow 2 (graphLocalGroup Γ a') := default
  let Rq := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  let Tq := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ a')))
  have hparam := reduced_critical_terminal_quotient_omega_card h hc hab hd hb hcomm Tq Rq
  have hT := unitary_omega_card (by omega : 0 < k) htm Tq
  have hy : (Q Γ beta).relIndex (V Γ a' 1) = 2^k :=
    (reduced_noncentral_opposite_omega_index_of h models hc hab hd hb hcomm hne hnd R).trans
      (hparam.symm.trans hT)
  have hx : (Q Γ a').relIndex (V Γ beta 1) = 2^k :=
    (reduced_critical_paired_core_indices_eq h models hc hab hd hb hcomm hne).trans hy
  have hfour : 4 ≤ 2^k := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk
  have hlo := reduced_ending_unitary_large_actor_field_square h hc hab hd hb hcomm hk htm
    (hx.symm ▸ hfour)
  have hup := reduced_terminal_fixed_index_le_twice h models hc hab hd hb hcomm w hm hu
  rw [hy] at hup
  have hbound := hlo.trans hup
  nlinarith

/-- Positive-parameter Suzuki terminal quotients are incompatible with
the same binary moving neighbor, by the original ending field-square bound. -/
theorem reduced_suzuki_terminal_impossible
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    {m : ℕ} (hmpos : 0 < m)
    (e : (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (graphLocalGroup Γ a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hr : primeRank 2 (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≤ 2*m+1 := by
    rw [primeRank_congr 2 e]
    exact (BenderSuzuki.MatrixGroups.suzuki_two_rank m hmpos).le
  have hy := (source_ending_rank_actor_bounds ht d hc hab hd hb hcomm (2*m+1) hr).2
  have hlo := reduced_ending_suzuki_field_square h hc hab hd hb hcomm m e
  have hup := reduced_terminal_fixed_index_le_twice h models hc hab hd hb hcomm w hm hu
  have hbound := hlo.trans (hup.trans (Nat.mul_le_mul_right 2 hy))
  have hfour : 4 ≤ 2^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*m+1)
  nlinarith

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
