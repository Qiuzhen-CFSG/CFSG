module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.AlternatingFive
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.SylowLocalCore
/-!
# Natural L₂ Borels in the original constrained local family

For K in the fixed family L(G₁,S), a genuine natural L₂ block identifies
its literal core quotient with SL₂ over the given even field. Sylow
conjugacy marks S∩K by the upper unipotent subgroup. The unique maximal
overgroup theorem puts M_Z∩K inside the corresponding Borel. Consequently
O₂(M_Z∩K)=S∩K, and N_{M_Z}(K) preserves that Borel by characteristicity.
These assertions require neither S-normalization nor ambient C-componenthood.

The chosen-component applications retain the original Thompson movement,
the pre-exclusion prime, and both exchanged-plane sizes. This is the upper
containment in the source Borel argument. The reverse containment, using
15.1.19(2) on the orbit Borel, and reconstruction of a block from the rank-one
FF image remain obligations of the catalogue owner. No full rank-one
alternative or catalogue exhaustiveness is claimed here.

Source: Aschbacher--Smith 15.1.20, third paragraph of the proof, printed
p.1094; the natural L₂ block is C.1.12, printed p.124.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem sylow_le_marked (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    d.S ≤ d.MZ := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  refine le_inf d.S_le_G1 ?_
  intro x hx
  apply hMc.2
  intro z hz
  exact (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm

/-- Every proper marked overgroup of the literal Sylow intersection in a
natural L₂ block is contained in its Borel. -/
theorem localFamily_linearTwo_borel_bound (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.MZ ⊓ K ≤ (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hPK : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hPA : (P : Subgroup K) ≤ d.MZ.subgroupOf K := by
    intro x hx
    exact d.sylow_le_marked hu ((hP ▸ mem_map_of_mem K.subtype hx).1)
  have hA : d.MZ.subgroupOf K ≠ ⊤ := fun he => hout (subgroupOf_eq_top.mp he)
  have hn := Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
    q hq P hk (d.MZ.subgroupOf K) hPA hA
  intro x hx
  exact ⟨⟨x,hx.2⟩,hPK ▸ hn hx.1,rfl⟩

/-- The literal core quotient has a matrix marking carrying S∩K to the
upper root subgroup and the corresponding Borel to the upper triangular
subgroup. The original marked intersection maps into that same Borel. -/
theorem localFamily_linearTwo_coordinates (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
        ((d.S ⊓ K).subgroupOf K).map q = Matrix.SpecialLinearGroup.upperUnipotent F ∧
        normalizer ((d.S ⊓ K).subgroupOf K : Set K) =
          (Matrix.SpecialLinearGroup.rankOneBorel F).comap q ∧
        (d.MZ.subgroupOf K).map q ≤ Matrix.SpecialLinearGroup.rankOneBorel F := by
  have hbound := d.localFamily_linearTwo_borel_bound hu hK hout hb
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hPK : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q₀ := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq₀ : Function.Surjective q₀ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective hq₀
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F) R
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  let e := m.quotientIso.trans (MulAut.conj a)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hp : (P : Subgroup K).map q = Matrix.SpecialLinearGroup.upperUnipotent F := by
    change (P : Subgroup K).map ((MulAut.conj a).toMonoidHom.comp q₀) = _
    rw [←map_map]
    change ((a • R : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F)) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = _
    rw [ha]
    rfl
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hn : (Matrix.SpecialLinearGroup.rankOneBorel F).comap q = normalizer (P : Set K) := by
    change (normalizer (Matrix.SpecialLinearGroup.upperUnipotent F : Set _)).comap q = _
    rw [←hp,comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hk]
    rfl
  refine ⟨F,inferInstance,inferInstance,inferInstance,hF,e,?_,?_,?_⟩
  · exact hPK ▸ hp
  · exact hPK ▸ hn.symm
  · apply map_le_iff_le_comap.mpr
    rw [hn]
    intro x hx
    obtain ⟨y,hy,he⟩ := hbound (show (x : G) ∈ d.MZ ⊓ K from ⟨hx,x.property⟩)
    have he' : y = x := Subtype.ext he
    change x ∈ normalizer ((P : Subgroup K) : Set K)
    rw [hPK]
    exact he' ▸ hy

/-- The marked intersection has exactly S∩K as its embedded two-core. -/
theorem localFamily_linearTwo_core (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    (d.MZ ⊓ K).pCoreIn 2 = d.S ⊓ K := by
  have hPA : d.S ⊓ K ≤ d.MZ ⊓ K := inf_le_inf_right K (d.sylow_le_marked hu)
  have hn : d.MZ ⊓ K ≤ normalizer (d.S ⊓ K : Set G) := by
    have hN := ((d.S ⊓ K).subgroupOf K).le_normalizer_map K.subtype
    rw [map_subgroupOf_eq_of_le inf_le_right] at hN
    exact (d.localFamily_linearTwo_borel_bound hu hK hout hb).trans hN
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.MZ ⊓ K ≤ K from inf_le_right) (hP ▸ hPA)
  exact le_antisymm ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) hPA hn)

/-- The source normalizer of K in M_Z preserves its literal Borel. No
S-normalization or ambient C-componenthood of K is assumed. -/
theorem localFamily_linearTwo_borel_normalized (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    d.MZ ⊓ normalizer (K : Set G) ≤
      normalizer ((normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype : Set G) := by
  have hnA : d.MZ ⊓ normalizer (K : Set G) ≤ normalizer (d.MZ ⊓ K : Set G) :=
    (le_inf (inf_le_left.trans d.MZ.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hnP : d.MZ ⊓ normalizer (K : Set G) ≤ normalizer (d.S ⊓ K : Set G) := by
    change d.MZ ⊓ normalizer (K : Set G) ≤ normalizer ((d.S ⊓ K : Subgroup G) : Set G)
    rw [←d.localFamily_linearTwo_core hu hK hout hb]
    exact hnA.trans (normalizer_le_normalizer_characteristic_image (d.MZ ⊓ K)
      (pCore 2 (d.MZ ⊓ K : Subgroup G)))
  have hB : (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype =
      K ⊓ normalizer (d.S ⊓ K : Set G) := by
    rw [←subgroupOf_normalizer_eq (show d.S ⊓ K ≤ K from inf_le_right)]
    rw [subgroupOf_map_subtype]
    exact inf_comm _ _
  rw [hB]
  exact (le_inf inf_le_right (hnP.trans (normalizer (d.S ⊓ K : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- Natural rank-one geometry on the original selected component, before
exchanged selection; the full Borel equality remains a separate obligation. -/
theorem PreExclusionSource.constrained_linearTwo_geometry
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p n : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hb : IsL2EvenBlock d.L n) :
    d.ML ≤ (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype ∧
      d.ML.pCoreIn 2 = d.SL ∧
      d.MZ ⊓ normalizer (d.L : Set G) ≤
        normalizer ((normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype : Set G) ∧
      ⁅d.L, elementaryAbelianMaxJ d.S⁆ = d.L := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  exact ⟨d.localFamily_linearTwo_borel_bound hu hk d.L_not_le_MZ hb,
    d.localFamily_linearTwo_core hu hk d.L_not_le_MZ hb,
    d.localFamily_linearTwo_borel_normalized hu hk d.L_not_le_MZ hb,
    (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
      d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩

/-- The later exchanged application preserves both source plane sizes. -/
theorem ExchangedSource.constrained_linearTwo_geometry
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource) {n : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hb : IsL2EvenBlock d.L n) :
    d.ML ≤ (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype ∧
      d.ML.pCoreIn 2 = d.SL ∧
      d.MZ ⊓ normalizer (d.L : Set G) ≤
        normalizer ((normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype : Set G) ∧
      ⁅d.L, elementaryAbelianMaxJ d.S⁆ = d.L := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  exact ⟨d.localFamily_linearTwo_borel_bound hu hk d.L_not_le_MZ hb,
    d.localFamily_linearTwo_core hu hk d.L_not_le_MZ hb,
    d.localFamily_linearTwo_borel_normalized hu hk d.L_not_le_MZ hb,
    (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
      d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
