module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryInvolutions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaCommutator

/-!
# The terminal unitary comparison in DGS 8.3

The field-square estimate extends from the marked edge to every elementary
actor at any vertex in the moving vertex's orbit, by Sylow and graph
conjugacy. Distinct preceding and moving Sylows identify the literal product
of core indices. The two reverse-intersection cases then give q² ≤ a₂ or
q² ≤ a₁ b₁ on the original subgroups.

If the full quotient omega-center failed the desired commutator inclusion,
the moving actor would be a proper subgroup of that omega-center, giving
b₁ < q. The paired comparisons a₁² ≤ a₂q and a₂² ≤ a₁q consequently exclude
both reverse-intersection cases. This proves the terminal source argument
with those two comparisons explicit. Their residual-factor and natural-case
proofs, followed by 8.4--8.7, remain with the Chapter 8 owner.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), 8.3,
printed pp.135--137. The original quotient, scalar kernels, full edge and
arbitrary critical orientation are preserved. The literal reduced-source
consumer is in UnitaryComparisonApplication.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

private theorem bound_from_one_sylow (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (R : Sylow 2 (d.localGroup v)) (c : ℕ)
    (hlower : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype →
      ¬ A ≤ Q (family P) v → c ≤ (centralizer (A : Set G)).relIndex (Z (family P) v))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ d.localGroup v) (hAQ : ¬ A ≤ Q (family P) v) :
    c ≤ (centralizer (A : Set G)).relIndex (Z (family P) v) := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 (A.subgroupOf L)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L T R
  let e := MulAut.conj (g : G)
  let A' := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hAS : A' ≤ (R : Subgroup L).map L.subtype := by
    rintro x ⟨a,ha,rfl⟩
    have hx : (MulAut.conj g) (⟨a,hAL ha⟩ : L) ∈ (R : Subgroup L) := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hAT ha)
    exact mem_map_of_mem L.subtype hx
  have hgfix : (g : G) • v = v := d.local_le v g.property
  have hQ : (Q (family P) v).map e.toMonoidHom = Q (family P) v := by
    rw [←Q_translate,hgfix]
  have hZ : (Z (family P) v).map e.toMonoidHom = Z (family P) v := by
    rw [←Z_translate,hgfix]
  have hA'Q : ¬ A' ≤ Q (family P) v := by
    rw [←hQ]
    exact fun hh => hAQ ((map_le_map_iff_of_injective e.injective).mp hh)
  have hh := hlower A' inferInstance hAS hA'Q
  rw [←hZ,←centralizer_map_equiv A e,relIndex_map_map_of_injective _ _ e.injective] at hh
  exact hh

private theorem bound_at_same_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type) (c : ℕ)
    (hlower : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ d.localGroup w → ¬ A ≤ Q (family P) w →
      c ≤ (centralizer (A : Set G)).relIndex (Z (family P) w))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ d.localGroup v) (hAQ : ¬ A ≤ Q (family P) v) :
    c ≤ (centralizer (A : Set G)).relIndex (Z (family P) v) := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  let e := MulAut.conj g
  let A' := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hAL' : A' ≤ d.localGroup (g • v) := by
    rw [d.conjugate]
    exact map_mono hAL
  have hAQ' : ¬ A' ≤ Q (family P) (g • v) := by
    rw [Q_translate]
    exact fun hh => hAQ ((map_le_map_iff_of_injective e.injective).mp hh)
  have hh := hlower A' inferInstance hAL' hAQ'
  rw [Z_translate,←centralizer_map_equiv A e,
    relIndex_map_map_of_injective _ _ e.injective] at hh
  exact hh

/-- The unitary field-square estimate applies to every elementary actor at
any vertex in the moving vertex's orbit. The marked edge containment is
constructed by Sylow conjugacy, and then transported through the graph action. -/
theorem source_moving_unitary_orbit_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
      IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n))
    {v : Vertex (family P)} (ht : v.type = w.val.type)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ d.localGroup v) (hAQ : ¬ A ≤ Q (family P) v) :
    (2^n)^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) v) := by
  apply bound_at_same_type h d ht ((2^n)^2) ?_ A hAL hAQ
  intro E hE hEL hEQ
  let := hE
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d w.property.symm
  apply bound_from_one_sylow h d w.val R ((2^n)^2) ?_ E hEL hEQ
  intro C hC hCR hCQ
  let := hC
  rw [hR] at hCR
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact source_moving_projective_unitary_involution_field_square_bound h hB d
      hc hab hd hb hcomm models w hm J hn hK hconj e C hCR hCQ
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    exact source_moving_special_unitary_involution_field_square_bound h hB d
      hc hab hd hb hcomm models w hm J hn hK hconj e C hCR hCQ

private theorem commutator_le_of_quotient_image_le
    (L Q A Y Z H : Subgroup G) {D : Type*} [Group D] (q : L →* D)
    (hk : q.ker = Q.subgroupOf L) (_hAL : A ≤ L) (hYL : Y ≤ L)
    (hQZ : Q ≤ centralizer (Z : Set G))
    (hi : (Y.subgroupOf L).map q ≤ (A.subgroupOf L).map q)
    (hAZ : ⁅A,Z⁆ ≤ H) : ⁅Y,Z⁆ ≤ H := by
  apply commutator_le.mpr
  intro y hy z hz
  obtain ⟨a,ha,he⟩ := hi (mem_map_of_mem q (show (⟨y,hYL hy⟩ : L) ∈ Y.subgroupOf L from hy))
  have hk' : a⁻¹ * (⟨y,hYL hy⟩ : L) ∈ q.ker := by
    change q (a⁻¹ * ⟨y,hYL hy⟩) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  rw [hk] at hk'
  change (a : G)⁻¹*y ∈ Q at hk'
  have hcz : ((a : G)⁻¹*y)*z*((a : G)⁻¹*y)⁻¹ = z := by
    rw [←hQZ hk' z hz,mul_inv_cancel_right]
  have heq : y*z*y⁻¹ = (a : G)*z*(a : G)⁻¹ := by
    calc
      y*z*y⁻¹ = (a : G)*(((a : G)⁻¹*y)*z*((a : G)⁻¹*y)⁻¹)*(a : G)⁻¹ := by group
      _ = (a : G)*z*(a : G)⁻¹ := by rw [hcz]
  have hh := commutator_le.mp hAZ (a : G) ha z hz
  change (a : G)*z*(a : G)⁻¹*z⁻¹ ∈ H at hh
  change y*z*y⁻¹*z⁻¹ ∈ H
  rwa [heq]

/-- A failure of 8.3 forces a proper moving image in the original quotient
omega-center. In particular its original core index is strictly below any
binary rank bound for that quotient. -/
theorem source_omega_counterexample_actor_lt (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (M : IsRankOneModel (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)))
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (n : ℕ) (hr : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ n)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆) :
    (Q (family P) w.val).relIndex (V (family P) beta 1 ⊓ Q (family P) a') < 2^n := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w.val
  let A := V F beta 1 ⊓ Q F a'
  let Y := quotientSylowOmegaPreimage L R
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let S := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let O := omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L))
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  have hb3 := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAL := (source_moving_actor h d hc hab hd hb hcomm w hm).2.1
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact inf_le_right.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property)
  have hAS : (A.subgroupOf L).map q ≤ S := by
    apply map_mono
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hAO : (A.subgroupOf L).map q ≤ O :=
    source_rank_one_elementary_le_sylow_omega M S _ hAS
  have hcard : Nat.card ((A.subgroupOf L).map q) = (Q F w.val).relIndex A :=
    BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F w.val) A q
      (local_quotient_kernel F d w.val (MulEquiv.refl _)) hAL
  have hO : Nat.card O ≤ 2^n := (primeRank_le_iff_elementary_card_le _).mp hr O inferInstance
  by_contra! hge
  change 2^n ≤ (Q F w.val).relIndex A at hge
  have he : (A.subgroupOf L).map q = O := eq_of_le_of_card_ge hAO (by omega)
  apply hbad
  apply commutator_le_of_quotient_image_le L (Q F w.val) A Y (Z F w.val) _ q
    (local_quotient_kernel F d w.val (MulEquiv.refl _)) hAL (map_subtype_le _)
    (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1))
  · rw [he,quotientSylowOmegaPreimage_image]
    exact le_rfl
  · exact commutator_mono le_rfl (Z_neighbor_le_V F w.property)

/-- The preceding and moving edge Sylows are distinct. Their intersection
with the elementary span therefore lies in the ending core. This is the
subgroup identity needed to multiply the original a₁ and b₁ indices in 8.3. -/
theorem source_moving_core_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (M : IsRankOneModel (d.localGroup a' ⧸ pCore 2 (d.localGroup a'))) :
    V (family P) beta 1 ⊓ Q (family P) w.val ≤ Q (family P) a' := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let A := V F beta 1
  let D := A ⊓ Q F w.val
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  obtain ⟨_,hb3,_,_,prev,hp,_,hAP,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hp
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d w.property
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact hAP.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hp.symm)
  have hAL : A ≤ L := hAR.trans (map_subtype_le _)
  have hDT : D ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    exact inf_le_right.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property.symm)
  let : IsElementaryAbelian 2 (D.subgroupOf L) := IsElementaryAbelian.subgroupOf (inf_le_left.trans hAL)
  by_contra hn
  have he : ¬ D.subgroupOf L ≤ pCore 2 L := by
    intro hh
    apply hn
    rw [←localGroup_core_eq F d a']
    intro x hx
    exact ⟨⟨x,hAL hx.1⟩,hh hx,rfl⟩
  have hRT := local_sylow_eq_of_elementary_escape M R T (D.subgroupOf L)
    (by intro x hx; obtain ⟨y,hy,he⟩ := hAR hx.1; exact (Subtype.ext he : y=x) ▸ hy)
    (by intro x hx; obtain ⟨y,hy,he⟩ := hDT hx; exact (Subtype.ext he : y=x) ▸ hy) he
  apply source_span_escapes_moving_edge h hB d hc hab hd hb hcomm M w hm
  exact hAR.trans (hRT ▸ hT ▸ pCoreIn_le 2 _)

private theorem core_index_product (U Q K : Subgroup G) (h : U ⊓ Q ≤ K) :
    Q.relIndex (U ⊓ K) * K.relIndex U = Q.relIndex U := by
  rw [inf_comm U K,relIndex_inf_mul_relIndex]
  rw [←inf_relIndex_right (Q ⊓ K) U,←inf_relIndex_right Q U]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,h ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩

/-- The two actual source alternatives at the end of 8.3: a centralizing
reverse intersection gives q² ≤ a₂; a moving reverse intersection gives
q² ≤ a₁ b₁. Both estimates retain the original cores and moving neighbor. -/
theorem source_unitary_reverse_index_alternatives (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
      IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n)) :
    let F := family P
    (2^n)^2 ≤ (Q F beta).relIndex (V F a' 1) ∨
      (2^n)^2 ≤ (Q F a').relIndex (V F beta 1) *
        (Q F w.val).relIndex (V F beta 1 ⊓ Q F a') := by
  let := finite_endpoints h
  let F := family P
  let A := V F beta 1 ⊓ Q F a'
  let E := Z F w.val ⊓ Q F beta
  have hb3 := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  let := CommutingOneProfile.source_center_elementary h w.val
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : Finite (Z F w.val) := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  have hVP (v : Vertex F) : V F v 1 ≤ stabilizer F v :=
    V_le_stabilizer_of_dist_add_le_b F h.generate v v 1 (by simp only [SimpleGraph.dist_self,zero_add]; exact hb.le)
  let : Finite (V F beta 1) := Finite.of_injective (inclusion (hVP beta)) (inclusion_injective _)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion (hVP a')) (inclusion_injective _)
  by_cases hz : ⁅E,V F beta 1⁆ = ⊥
  · left
    obtain ⟨_,hAL,_,hAQ,_⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
    have hl := source_moving_unitary_orbit_bound h hB d hc hab hd hb hcomm models w hm hn hu rfl A hAL hAQ
    have hEC : E ≤ centralizer (A : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp hz).trans (centralizer_le inf_le_left)
    have hi : (centralizer (A : Set G)).relIndex (Z F w.val) ≤ (Q F beta).relIndex (Z F w.val) := by
      have hh := relIndex_le_of_le_left hEC ((E.subgroupOf (Z F w.val)).index_ne_zero_of_finite)
      simpa only [E,inf_relIndex_left] using hh
    exact hl.trans (hi.trans (relIndex_le_of_le_right (Z_neighbor_le_V F w.property)
      (((Q F beta).subgroupOf (V F a' 1)).index_ne_zero_of_finite)))
  · right
    have hex : ∃ z : (graph F).neighborSet beta, ⁅E,Z F z.val⁆ ≠ ⊥ := by
      by_contra! hall
      apply hz
      apply commutator_eq_bot_iff_le_centralizer.mpr
      apply le_centralizer_iff.mpr
      rw [V_one_eq_sup_neighbors]
      apply sup_le
      · exact (Z_centralizes_Q F beta (source_Z_Q_U h beta).1).trans (centralizer_le inf_le_right)
      · exact iSup_le (fun z => le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hall z)))
    obtain ⟨z,hzmove⟩ := hex
    have heven : Even ((graph F).dist beta a') := by
      obtain ⟨k,hk⟩ := (source_critical_geometry h d hc hab hd hb hcomm).1
      refine ⟨k,?_⟩
      change (graph (family P)).dist beta a' = k+k
      omega
    have ht := (even_dist_iff F h.generate beta a').mp heven
    have hzt : z.val.type = w.val.type := by
      have hz' := z.property.1
      have hw' := w.property.1
      cases hzt : z.val.type <;> cases hwt : w.val.type <;>
        cases hbt : beta.type <;> cases het : a'.type <;> simp_all
    have hEL : E ≤ d.localGroup z.val := pGroup_le_localGroup F d z.val E
      (IsElementaryAbelian.isPGroup 2 E)
      (inf_le_right.trans ((source_Z_Q_U h beta).2.trans
        ((ballKernel_one_le_edge F z.property).trans inf_le_right)))
    have hEQ : ¬ E ≤ Q F z.val := by
      intro he
      exact hzmove (commutator_eq_bot_iff_le_centralizer.mpr
        (he.trans (le_centralizer_iff.mp (Z_centralizes_Q F z.val (source_Z_Q_U h z.val).1))))
    have hl := source_moving_unitary_orbit_bound h hB d hc hab hd hb hcomm models w hm hn hu hzt E hEL hEQ
    have hQC : Q F w.val ≤ centralizer (E : Set G) :=
      (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1)).trans
        (centralizer_le inf_le_left)
    let : Finite (Z F z.val) := Finite.of_injective (inclusion (Z_le_stabilizer F z.val)) (inclusion_injective _)
    have hi := relIndex_le_of_le_left hQC (((Q F w.val).subgroupOf (Z F z.val)).index_ne_zero_of_finite)
    have hj := relIndex_le_of_le_right (Z_neighbor_le_V F z.property)
      (((Q F w.val).subgroupOf (V F beta 1)).index_ne_zero_of_finite)
    have he := core_index_product (V F beta 1) (Q F w.val) (Q F a')
      (source_moving_core_intersection h hB d hc hab hd hb hcomm w hm (models a'))
    exact hl.trans (hi.trans (hj.trans_eq (he.symm.trans (Nat.mul_comm _ _))))

private theorem paired_indices_le (x y q : ℕ)
    (hx : x^2 ≤ y*q) (hy : y^2 ≤ x*q) : x ≤ q ∧ y ≤ q := by
  rcases le_total x y with h | h
  · have hprod := Nat.mul_le_mul_right q h
    have hyq : y ≤ q := by nlinarith
    exact ⟨h.trans hyq,hyq⟩
  · have hprod := Nat.mul_le_mul_right q h
    have hxq : x ≤ q := by nlinarith
    exact ⟨hxq,h.trans hxq⟩

/-- The literal terminal argument of DGS 8.3. The two paired comparisons
(8.3)(2) remain explicit; all actor placements, reverse-intersection cases,
field-square estimates and the equality/saturation obstruction are proved.
The source owner must still construct those comparisons from the residual
factor actions before this becomes the unconditional source theorem. -/
theorem source_omega_commutator_of_paired_indices (h : LocallyRankOneTriple P B)
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
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hpair : ∀ n : ℕ, 2 ≤ n →
      (ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
        IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n)) →
      (Q (family P) a').relIndex (V (family P) beta 1) ^ 2 ≤
        (Q (family P) beta).relIndex (V (family P) a' 1) * 2^n ∧
      (Q (family P) beta).relIndex (V (family P) a' 1) ^ 2 ≤
        (Q (family P) a').relIndex (V (family P) beta 1) * 2^n) :
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ := by
  let := finite_endpoints h
  let : Finite (d.localGroup w.val) :=
    Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  by_contra hbad
  obtain ⟨n,hn,hu⟩ := (source_moving_omega_commutator_or_large_unitary h hB d
    hc hab hd hb hcomm models w hm R hR).resolve_left hbad
  have hr : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ n := by
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e]
      exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  have hlt := source_omega_counterexample_actor_lt h d hc hab hd hb hcomm w hm
    (models w.val) R hR n hr hbad
  obtain ⟨hx,hy⟩ := paired_indices_le _ _ _ (hpair n hn hu).1 (hpair n hn hu).2
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  rcases source_unitary_reverse_index_alternatives h hB d hc hab hd hb hcomm models w hm hn hu with hl | hl
  · nlinarith
  · have hmul := Nat.mul_le_mul_right
      ((Q (family P) w.val).relIndex (V (family P) beta 1 ⊓ Q (family P) a')) hx
    nlinarith

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
