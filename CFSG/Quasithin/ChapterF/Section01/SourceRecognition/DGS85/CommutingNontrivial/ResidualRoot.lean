module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryResidualRoot
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaCommutator

/-!
# The residual intersection lies over the quotient omega-center

Write T for the full moving-edge Sylow and E for O²(L_alpha'). The known
omega displacement lies in C_Z_lambda(E). If T lies in E Q_lambda, T fixes
that displacement, and the actual unitary module calculation contradicts
the assumed failure of 8.3. Thus T ∩ E Q_lambda is proper in T.

The original edge normalizer preserves this intersection and maps onto the
quotient Sylow normalizer. The unitary invariant-subgroup dichotomy therefore
puts its image in Ω₁(Z(T/Q_lambda)). This proves the upper inclusion needed
for the residual action; it does not assert the reverse inclusion, the paired
square inequalities, or the subsequent Chapter 8 conclusions.
Source: DGS, Groups and Graphs (1985), proof of 8.3, printed pp.135–136.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

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

private theorem source_omega_commutator_of_sylow_fixed (h : LocallyRankOneTriple P B)
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
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n))
    (hroot : ⁅(R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype,
      ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆⁆ = ⊥) :
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
  have hfix : Coinvariants.ker (ρ.comp (omegaCenterIn (S : Subgroup D)).subtype) ≤ fixedSpace ρ S := by
    rw [←hYS]
    have hmoved : Coinvariants.ker (ρ.comp ((Y.subgroupOf L).map q).subtype) ≤
        δ.imageSpace ⁅Y,Z F w.val⁆ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨t,v⟩,rfl⟩
      obtain ⟨l,hl,he⟩ := t.property
      change ρ t.val v - v ∈ δ.imageSpace ⁅Y,Z F w.val⁆
      rw [←he]
      exact δ.displacement_range_le_imageSpace_of_commutator_le Y ⁅Y,Z F w.val⁆ le_rfl l hl ⟨v,rfl⟩
    intro v hv r
    obtain ⟨l,hl,he⟩ := r.property
    change ρ r.val v = v
    rw [←he]
    exact δ.fixed_on_imageSpace_of_commutator_le
      ((R : Subgroup L).map L.subtype) ⁅Y,Z F w.val⁆ hroot.le l
      (mem_map_of_mem L.subtype hl) v (hmoved hv)
  apply center_commutator_le_of_moved_le L (Z F w.val) A Y _ hZL δ.normalized hYL q ρ hact
  · rw [hYS]
    exact unitary_sylow_moved_le_actor hn hu ρ S hquad
      (bot_unique ((fixedSpace_antitone ρ le_top).trans hres.le)) hfix _ hAO hne
  · exact commutator_mono le_rfl (Z_neighbor_le_V F w.property)

/-- Under a counterexample to 8.3, the full moving-edge Sylow cannot lie
in O²(L_alpha') Q_lambda. Thus the printed T₀ has a proper image in the
moving quotient Sylow. The residual denominator and both unitary covers
are handled on their actual source subgroups. -/
theorem source_counterexample_residual_edge_proper (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆) :
    ¬ (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype ≤
      (pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype ⊔ Q (family P) w.val := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w.val
  let E := (pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype
  let C := Z F w.val ⊓ centralizer (E : Set G)
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  intro hall
  have hEC : E ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hQC : Q F w.val ≤ centralizer (C : Set G) :=
    (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1)).trans
      (centralizer_le inf_le_left)
  have hTC := hall.trans (sup_le hEC hQC)
  have hmove := source_omega_displacement_residual_fixed h hB d hc hab hd hb hcomm models w hm hescape R hR
  have hroot : ⁅(R : Subgroup L).map L.subtype,⁅quotientSylowOmegaPreimage L R,Z F w.val⁆⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hTC.trans (centralizer_le hmove))
  obtain ⟨n,hn,hu⟩ := (source_moving_omega_commutator_or_large_unitary h hB d hc hab hd hb hcomm
    models w hm R hR).resolve_left hbad
  exact hbad (source_omega_commutator_of_sylow_fixed h hB d hc hab hd hb hcomm models w hm
    (MulEquiv.refl (L ⧸ pCore 2 L)) R hR hn hu hroot)


/-- The normalizer-invariant residual intersection has image in the
quotient omega-center. The full-Sylow alternative is excluded by the actual
unitary center action, rather than by an assumed quotient identity. -/
theorem source_counterexample_residual_edge_le_omega (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆) :
    ((R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype) ⊓
      ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype ⊔ Q (family P) w.val) ≤
      quotientSylowOmegaPreimage (d.localGroup w.val) R := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w.val
  let T := (R : Subgroup L).map L.subtype
  let E := (pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype
  let D := E ⊔ Q F w.val
  let T₀ := T ⊓ D
  let N := (normalizer (R : Set L)).map L.subtype
  let X := T₀.subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let S := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let A := X.map q
  have hNend : N ≤ stabilizer F a' := by
    have he := (source_edge_local_normalizer h d w.property.symm (models w.val) R hR).2
    rintro _ ⟨l,hl,rfl⟩
    have hl' : l ∈ (stabilizer F a').subgroupOf L := he.symm ▸ hl
    exact hl'
  have hNL : N ≤ normalizer (d.localGroup a' : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.conjugate g a').symm.trans (congrArg d.localGroup (hNend hg))
  have hNE : N ≤ normalizer (E : Set G) :=
    hNL.trans (normalizer_le_normalizer_characteristic_image (d.localGroup a') (pResidual 2 (d.localGroup a')))
  have hNQ : N ≤ normalizer (Q F w.val : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (Q_translate F g w.val).symm.trans
      (congrArg (Q F) (((map_subtype_le _).trans (d.local_le w.val)) hg))
  have hNT : N ≤ normalizer (T : Set G) := (R : Subgroup L).le_normalizer_map L.subtype
  have hNX : N ≤ normalizer (T₀ : Set G) :=
    (le_inf hNT ((le_inf hNE hNQ).trans (normalizer_inf_normalizer_le_normalizer_sup E (Q F w.val)))).trans
      inf_normalizer_le_normalizer_inf
  have hXS : X ≤ R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hx.1
    exact (Subtype.ext he : y=x) ▸ hy
  have hnX : normalizer (R : Set L) ≤ normalizer (X : Set L) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    exact le_normalizer_iff.mp hNX g (mem_map_of_mem L.subtype hg) x hx
  have hnA : normalizer (S : Set (L ⧸ pCore 2 L)) ≤ normalizer (A : Set _) := by
    change normalizer ((R : Subgroup L).map q : Set (L ⧸ pCore 2 L)) ≤ _
    rw [←R.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)]
    exact (map_mono hnX).trans (X.le_normalizer_map q)
  obtain ⟨n,hn,hu⟩ := (source_moving_omega_commutator_or_large_unitary h hB d hc hab hd hb hcomm
    models w hm R hR).resolve_left hbad
  have hA : A ≤ omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L)) := by
    rcases unitary_sylow_invariant_dichotomy hn hu S A (map_mono hXS) hnA with hlo | he
    · exact hlo
    · exfalso
      apply source_counterexample_residual_edge_proper h hB d hc hab hd hb hcomm models w hm hescape R hR hbad
      rintro _ ⟨r,hr,rfl⟩
      have hrA : q r ∈ A := by rw [he]; exact mem_map_of_mem q hr
      obtain ⟨x,hx,hxr⟩ := hrA
      have hk : x⁻¹*r ∈ q.ker := by
        change q (x⁻¹*r) = 1
        rw [map_mul,map_inv,hxr,inv_mul_cancel]
      change x⁻¹*r ∈ (QuotientGroup.mk' (pCore 2 L)).ker at hk
      rw [QuotientGroup.ker_mk'] at hk
      have hkQ : (x : G)⁻¹*(r : G) ∈ Q F w.val := by
        rw [←localGroup_core_eq F d w.val]
        exact mem_map_of_mem L.subtype hk
      have hD : (x : G)⁻¹*(r : G) ∈ D := (show Q F w.val ≤ D from le_sup_right) hkQ
      have hh := D.mul_mem hx.2 hD
      change (x : G)*((x : G)⁻¹*(r : G)) ∈ D at hh
      change (r : G) ∈ D
      simpa only [mul_inv_cancel_left] using hh
  intro x hx
  have hXL : T₀ ≤ L := inf_le_left.trans (map_subtype_le _)
  exact ⟨⟨x,hXL hx⟩,hA (mem_map_of_mem q (show (⟨x,hXL hx⟩ : L) ∈ X from hx)),rfl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
