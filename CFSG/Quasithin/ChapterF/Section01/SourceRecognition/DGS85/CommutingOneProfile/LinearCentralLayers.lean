module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneCenterIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneSeparation
public import Theory.ElementaryAbelian.Injective

/-!
# The remaining central layer for every beta row of a linear-alpha branch

Write I_beta for the intersection of all neighboring alpha cores and let
beta' be a distinct beta vertex on an alpha turn. The already proved core
identities give the opposite-seed supplement and the remote-core separation.
Consequently I_beta intersect Q_beta' embeds in the original remote linear
quotient: it is elementary abelian of order at most the alpha field order.

The mixed core-center intersections make the product of this layer and
Z_alpha invariant under the alpha local group. Its commutator with Q_alpha
is then normalized by transitive groups at both endpoints and vanishes by
faithfulness. The actual edge Sylow puts the layer in Z_beta. In the
commuting branch this identifies it with Z_beta intersect Q_beta', and
remote-core separation makes the distinct beta centers disjoint.

All beta catalogue rows, both unitary quotient conventions, the full local
kernels and the original local quotient maps are retained. The linear alpha
marking and earlier local inputs remain explicit. Vanishing of this layer,
alpha row selection, the general center orders and the full (11.7)--(11.8)
profiles are further source obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (11.6), printed pp.172--173, using (11.3)(a,h), (11.4)--(11.5)
and faithful normalizer propagation (3.2)(c).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem linear_elementary_card {A : Type*} [Group A]
    (hp : IsPGroup 2 A) (f : A →* SL(2,k)) (hf : Function.Injective f) :
    IsElementaryAbelian 2 A ∧ Nat.card A ≤ Nat.card k := by
  obtain ⟨T,hT⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let j : A →* T := f.codRestrict T (fun a => hT ⟨a,rfl⟩)
  have hj : Function.Injective j := fun _ _ he => hf (congrArg Subtype.val he)
  let e := (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm
  let q := e.toMonoidHom.comp j
  have hq : Function.Injective q := e.injective.comp hj
  have hexp : Monoid.exponent (Multiplicative k) ∣ 2 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    change 2 • x.toAdd = 0
    rw [nsmul_eq_mul,CharP.cast_eq_zero k 2,zero_mul]
  let : IsElementaryAbelian 2 (Multiplicative k) :=
    { toIsMulCommutative := inferInstance, exponent_dvd_p := hexp }
  exact ⟨IsElementaryAbelian.of_injective q hq,
    Nat.card_le_card_of_injective q hq⟩

private def linear_quotient_at_conjugate (d : EarlierLocalTheorems (family P))
    (a : Vertex (family P)) (t : G)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (d.localGroup (t • a) ⧸ pCore 2 (d.localGroup (t • a))) ≃* SL(2,k) := by
  let e := (MulEquiv.subgroupCongr (d.conjugate t a)).trans
    ((d.localGroup a).equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans ea

private theorem linear_seed_supplement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
  obtain ⟨hp,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
  rw [sup_comm]
  exact alpha_supplement_of_pair_generation _ _ _ _ _ hp hcore
    ((source_Z_Q_U h a).1.trans (map_subtype_le _))

/-- The literal remaining layer in (11.6) embeds in a Sylow of the remote
linear quotient. In particular it is elementary of order at most |k|. -/
theorem source_linear_rankOne_intersection_layer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    IsElementaryAbelian 2 (neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) : Subgroup G) ∧
      Nat.card (neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) : Subgroup G) ≤ Nat.card k := by
  let := finite_endpoints h
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b)
  have hp : IsPGroup 2 J := (isPGroup_pCoreIn 2 _).to_le inf_le_right
  have hJH : J ≤ stabilizer (family P) (g • c) := inf_le_right.trans
    ((source_Z_Q_U h (g • b)).2.trans ((ballKernel_one_le_edge _
      ((Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc)).trans inf_le_right))
  have hJL := pGroup_le_localGroup (family P) d (g • c) J hp hJH
  obtain ⟨t,_,hta⟩ := locally_transitive (family P) (source_critical_one_adjacent hc hb).symm hbc
  have hta' : (g*t) • a = g • c := by rw [mul_smul,hta]
  have e : (d.localGroup (g • c) ⧸ pCore 2 (d.localGroup (g • c))) ≃* SL(2,k) :=
    hta' ▸ linear_quotient_at_conjugate d a (g*t) ea
  let H := d.localGroup (g • c)
  let j : J →* H := inclusion hJL
  let f := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))).comp j
  have hsupp := linear_seed_supplement h hB d hc hb hbc hac Ma Mb ea
  have hsep := source_rankOne_neighbor_intersection_separated h hB d hc hb hbc hac Ma Mb hsupp g hga hgb
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have he : e ((QuotientGroup.mk' (pCore 2 H)) (j x)) = 1 := hx
    rw [map_eq_one_iff e e.injective] at he
    have hxQ : (x : G) ∈ Q (family P) (g • c) := by
      rw [←localGroup_core_eq (family P) d (g • c)]
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (j x)).mp he)
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hsep ▸ (show (x : G) ∈ neighborCoreIntersection (family P) b ⊓
      Q (family P) (g • c) from ⟨x.property.1,hxQ⟩))
  exact linear_elementary_card hp f hf

private theorem stabilizer_normalizes_core (a : Vertex (family P)) :
    stabilizer (family P) a ≤ normalizer (Q (family P) a : Set G) :=
  (stabilizer (family P) a).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) a)))

private theorem stabilizer_normalizes_center (h : LocallyRankOneTriple P B)
    (a : Vertex (family P)) :
    stabilizer (family P) a ≤ normalizer (Z (family P) a : Set G) := by
  let := finite_endpoints h
  exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ a)).mp (Z_normal _ a)

private theorem core_le_adjacent_stabilizer (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Q (family P) a ≤ stabilizer (family P) b :=
  (source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)


/-- The remaining layer centralizes the actual alpha core for every beta row. -/
theorem source_linear_rankOne_layer_centralizes_core (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) ≤
      centralizer (Q (family P) a : Set G) := by
  let := finite_endpoints h
  have hsupp := linear_seed_supplement h hB d hc hb hbc hac Ma Mb ea
  let I := neighborCoreIntersection (family P) b
  let J := I ⊓ Q (family P) (g • b)
  let N := J ⊔ Z (family P) a
  let C := Z (family P) c ⊓ Q (family P) b
  let D := Z (family P) (g • c) ⊓ Q (family P) (g • b)
  have hab := source_critical_one_adjacent hc hb
  have hga' : g • a = a := hga
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [hga'] at hh
  have hIqa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  have hJqa : J ≤ Q (family P) a := inf_le_left.trans hIqa
  have hCQ : C ≤ Q (family P) b := inf_le_right
  have hCga : C ≤ stabilizer (family P) a := hCQ.trans (core_le_adjacent_stabilizer h hab.symm)
  have hDga : D ≤ stabilizer (family P) a := inf_le_right.trans
    (core_le_adjacent_stabilizer h hab'.symm)
  have hQaJ : Q (family P) a ≤ normalizer (J : Set G) :=
    (le_inf ((core_le_adjacent_stabilizer h hab).trans (neighborCoreIntersection_normalized _ b))
      (source_adjacent_core_normalizes_core h hab')).trans inf_normalizer_le_normalizer_inf
  have hQaN : Q (family P) a ≤ normalizer (N : Set G) :=
    (le_inf hQaJ ((Q_le_stabilizer _ a).trans (stabilizer_normalizes_center h a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hCJ : C ≤ centralizer (J : Set G) := inf_le_left.trans
    ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
      (centralizer_le (inf_le_left.trans (neighborCoreIntersection_le _ hbc.symm))))
  have hCN : C ≤ normalizer (N : Set G) :=
    (le_inf (hCJ.trans (Subgroup.centralizer_le_normalizer _))
      (hCga.trans (stabilizer_normalizes_center h a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJD : ⁅J,D⁆ ≤ Z (family P) a := by
    have h₁ : ⁅J,D⁆ ≤ Q (family P) a :=
      (commutator_mono hJqa le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hDga.trans (stabilizer_normalizes_core a)))
    have h₂ : ⁅J,D⁆ ≤ Z (family P) (g • c) :=
      (commutator_mono inf_le_right inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          (source_adjacent_core_normalizes_center h
            ((Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc).symm))
    have hid := congrArg (map (MulAut.conj g).toMonoidHom)
      (source_rankOne_mixed_center_intersections h hB d hc hb hbc Mb).2
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←Q_translate,←Z_translate,←Z_translate,hga'] at hid
    exact (le_inf h₁ h₂).trans (hid.le.trans inf_le_left)
  have hDN : D ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal N J (Z (family P) a) D N
      N.le_normalizer le_sup_left le_sup_right
    · exact hJD.trans le_sup_right
    · exact (le_normalizer_iff_commutator_le_left.mp
        (hDga.trans (stabilizer_normalizes_center h a))).trans le_sup_right
  have hnorm : d.localGroup a ≤ normalizer (N : Set G) := by
    rw [←source_rankOne_opposite_seed_generation h hB d hc hb hbc hac Ma Mb hsupp g hga hgb]
    exact sup_le (sup_le hCN hDN) hQaN
  let E := ⁅N,Q (family P) a⁆
  have hEJ : E ≤ J := by
    apply commutator_sup_le_of_relative_normal (Q (family P) a)
      J (Z (family P) a) (Q (family P) a) J hQaJ hJqa
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
    · exact le_normalizer_iff_commutator_le_left.mp hQaJ
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (source_core_centralizes_center h a))).le.trans bot_le
  have hEn : d.localGroup a ≤ normalizer (E : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change E.map (MulAut.conj t).toMonoidHom = E
    have hnmap : N.map (MulAut.conj t).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (hnorm ht)
    have hqmap : (Q (family P) a).map (MulAut.conj t).toMonoidHom = Q (family P) a :=
      mem_normalizer_iff_map_conj_eq.mp (stabilizer_normalizes_core a (d.local_le a ht))
    rw [map_commutator,hnmap,hqmap]
  have hE : E = ⊥ := by
    apply CommutingNontrivial.source_normalized_edge_eq_bot h hab E
      (hEJ.trans (le_inf (hJqa.trans (Q_le_stabilizer _ a))
        (hJqa.trans (core_le_adjacent_stabilizer h hab))))
    · intro v hv
      obtain ⟨t,ht,he⟩ := d.transitive a ⟨b,hab⟩ ⟨v,hv⟩
      exact ⟨t,hEn ht,he⟩
    · intro v hv
      obtain ⟨t,ht,he⟩ := source_neighbor_core_centralizer_transitive h hB hc hb hv
      exact ⟨t,Subgroup.centralizer_le_normalizer _
        (centralizer_le (hEJ.trans inf_le_left) ht.2),he⟩
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique ((commutator_mono le_sup_left le_rfl).trans hE.le))



/-- An elementary subgroup central in the actual edge Sylow lies in the beta center. -/
theorem source_elementary_central_edge_le_center (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)
    (hC : A ≤ centralizer ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 : Set G)) :
    A ≤ Z (family P) b := by
  let := finite_endpoints h
  obtain ⟨T,T',hTT⟩ := d.common_sylow b a hab.symm
  have he := sylow_image_eq_edge_core (stabilizer (family P) b)
    (stabilizer (family P) b ⊓ stabilizer (family P) a) inf_le_left
    (source_edge_core_sylow h hB hab.symm) T
    (le_inf (map_subtype_le _) (hTT ▸ map_subtype_le _))
  rw [inf_comm] at he
  have ho : A ≤ omegaCenterIn ((T : Subgroup (stabilizer (family P) b)).map
      (stabilizer (family P) b).subtype) := by
    rw [he]
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hA hx,hC hx,elemPow_eq_one_of_isElementaryAbelian x hx⟩
  exact ho.trans (le_iSup (fun R : Sylow 2 (stabilizer (family P) b) =>
    omegaCenterIn ((R : Subgroup (stabilizer (family P) b)).map
      (stabilizer (family P) b).subtype)) T)

/-- The elementary remaining layer lies in the actual beta center, with
no bound on either valence or the linear field degree. -/
theorem source_linear_rankOne_layer_le_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) ≤ Z (family P) b := by
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b)
  let : IsElementaryAbelian 2 J :=
    (source_linear_rankOne_intersection_layer h hB d hc hb hbc hac Ma Mb ea g hga hgb).1
  have hab := source_critical_one_adjacent hc hb
  have he := linear_seed_supplement h hB d hc hb hbc hac Ma Mb ea
  apply source_elementary_central_edge_le_center h hB d hab J
  · rw [he]
    exact (inf_le_left.trans (neighborCoreIntersection_le _ hab)).trans le_sup_right
  · rw [he]
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
        (centralizer_le (inf_le_left.trans (neighborCoreIntersection_le _ hbc.symm))))
    · exact le_centralizer_iff.mp
        (source_linear_rankOne_layer_centralizes_core h hB d hc hb hbc hac Ma Mb ea g hga hgb)

/-- The remaining intersection is literally Z_beta intersect Q_beta', and
its order is at most the alpha field order. Vanishing is a further step. -/
theorem source_linear_rankOne_layer_eq_center_inf (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) =
      Z (family P) b ⊓ Q (family P) (g • b) := by
  let := finite_endpoints h
  have hZb := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup b) (d.sylow_or_center b)
  have hZI : Z (family P) b ≤ neighborCoreIntersection (family P) b := by
    apply le_iInf
    intro v
    rw [hZb]
    exact (local_omega_le_neighbor_Z h d v.property).trans
      ((source_Z_Q_U h v.val).1.trans (map_subtype_le _))
  exact le_antisymm (le_inf
    (source_linear_rankOne_layer_le_center h hB d hc hb hbc hac Ma Mb ea g hga hgb) inf_le_right)
    (inf_le_inf_right _ hZI)

/-- Distinct beta centers on an alpha turn are disjoint in every beta row. -/
theorem source_linear_rankOne_beta_centers_disjoint (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Disjoint (Z (family P) b) (Z (family P) (g • b)) := by
  let := finite_endpoints h
  have hZb := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup b) (d.sylow_or_center b)
  have hZI : Z (family P) b ≤ neighborCoreIntersection (family P) b := by
    apply le_iInf
    intro v
    rw [hZb]
    exact (local_omega_le_neighbor_Z h d v.property).trans
      ((source_Z_Q_U h v.val).1.trans (map_subtype_le _))
  have hZgc : Z (family P) (g • b) ≤ Q (family P) (g • c) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      (hZI.trans (neighborCoreIntersection_le _ hbc.symm))
    rwa [←Z_translate,←Q_translate] at hh
  have hsep := source_rankOne_neighbor_intersection_separated h hB d hc hb hbc hac Ma Mb
    (linear_seed_supplement h hB d hc hb hbc hac Ma Mb ea) g hga hgb
  exact disjoint_iff.mpr (bot_unique ((inf_le_inf hZI hZgc).trans hsep.le))
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
