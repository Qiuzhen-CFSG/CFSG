module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadLift
public import Theory.Mathieu.M22.Properties.HexadMaximal
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups

/-!
# Generation of the full covered Mathieu carrier by the natural member and hexad

The full hexad lift H is a maximal subgroup of the original selected L.
The original escaping natural member K cannot lie in H: in the literal
M₂₂ quotient its image has order 960 and is normalized by the full original
Sylow. If that image lay in the hexad, the six-point quotient would have
order divisible by five. Its join with the Sylow must therefore be A₆,
where normality would force it to be all of A₆. This is impossible because
360 does not divide 960.

Maximality now gives K join H = L. Both the maximality and generation lift
through L → L/Z(L) → M₂₂, retaining the entire covering center. The source
application keeps the original marker, prime, row, G₁, M_Z, S and Q₁, and
all previously constructed hexad core and normalization clauses. Sylow
normalization of K is proved from the original source hypotheses.

This supplies the exact maximal overgroup and generation for the remaining
ambient M₂₂ exclusion; it does not itself exclude the configuration. The
original 15.1.20(2) and constrained 15.1.22 assembly remain open. Original
15.1.14 and whole-core A₆ reconstruction retain their existing producers.

Source: Aschbacher--Smith 15.1.20(2) and 15.1.22, printed pp.1094--1100;
I.2.2(6), p.412, and A.3.12--14 for the native hexad and local A₅ geometry.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M22CentralCover
open scoped Pointwise

private theorem natural_not_le_hexad
    (P : Sylow 2 M22) (A : Subgroup M22)
    (hPA : (P : Subgroup M22) ≤ normalizer (A : Set M22))
    (hc : Nat.card A = 960) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hPH : (P : Subgroup M22) ≤ MulAction.stabilizer M22 B) :
    ¬ A ≤ MulAction.stabilizer M22 B := by
  intro hAH
  let H := MulAction.stabilizer M22 B
  let q := m22HexadSixMap hB
  let f : A →* alternatingGroup (Fin 6) := q.comp (inclusion hAH)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.comap (inclusion hAH) := rfl
    rw [he,m22HexadSixMap_ker]
    let := m22HexadKernel_elementaryAbelian hB
    exact (IsElementaryAbelian.isPGroup 2 (m22SetAction B).ker).comap_of_injective (inclusion hAH)
      (inclusion_injective hAH)
  have hmul : Nat.card f.ker * Nat.card f.range = 960 := by
    have he := f.ker.card_mul_index
    rw [index_ker,hc] at he
    exact he
  have h5 : 5 ∣ Nat.card f.range := by
    have hd : 5 ∣ Nat.card f.ker * Nat.card f.range := hmul ▸ (by decide : 5 ∣ 960)
    rcases (Nat.prime_five.dvd_mul.mp hd) with hd | hd
    · obtain ⟨n,hn⟩ := hk.exists_card_eq
      rw [hn] at hd
      exact False.elim ((by decide : ¬ 5 ∣ 2) (Nat.prime_five.dvd_of_dvd_pow hd))
    · exact hd
  let Q := (P.subtype hPH).mapSurjective (m22HexadSixMap_surjective hB)
  have hQN : (Q : Subgroup (alternatingGroup (Fin 6))) ≤
      normalizer (f.range : Set (alternatingGroup (Fin 6))) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · rintro ⟨a,rfl⟩
      have hn := le_normalizer_iff.mp hPA x.val hx a a.property
      refine ⟨⟨x.val * a.val * x.val⁻¹,hn⟩,?_⟩
      change q (inclusion hAH ⟨x.val * a.val * x.val⁻¹,hn⟩) = _
      have he : inclusion hAH ⟨x.val * a.val * x.val⁻¹,hn⟩ =
          x * inclusion hAH a * x⁻¹ := rfl
      rw [he,map_mul,map_mul,map_inv]
      rfl
    · intro hy
      obtain ⟨a,ha⟩ := hy
      have hn := le_normalizer_iff.mp hPA x.val⁻¹ (P.inv_mem hx) a a.property
      refine ⟨⟨x.val⁻¹ * a.val * x.val,hn⟩,?_⟩
      change q (inclusion hAH ⟨x.val⁻¹ * a.val * x.val,hn⟩) = y
      have he : inclusion hAH ⟨x.val⁻¹ * a.val * x.val,hn⟩ =
          x⁻¹ * inclusion hAH a * x := rfl
      rw [he,map_mul,map_mul,map_inv]
      change (q x)⁻¹ * f a * q x = y
      change f a = q x * y * (q x)⁻¹ at ha
      rw [ha]
      group
  have htop : f.range ⊔ (Q : Subgroup (alternatingGroup (Fin 6))) = ⊤ := by
    by_contra hh
    have hd := h5.trans (card_dvd_of_le (show f.range ≤
      f.range ⊔ (Q : Subgroup (alternatingGroup (Fin 6))) from le_sup_left))
    rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour Q _ le_sup_right hh
      with he | he <;> rw [he] at hd <;> norm_num at hd
  have hn : f.range.Normal := by
    rw [←normalizer_eq_top_iff]
    apply top_unique
    rw [←htop]
    exact sup_le f.range.le_normalizer hQN
  let := hn
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
      (N := f.range) with he | he
  · rw [he,card_bot] at h5
    norm_num at h5
  · rw [he,card_top,nat_card_alternatingGroup,Nat.card_fin] at hmul
    norm_num at hmul
    omega

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}


/-- The full covered hexad is maximal in the original selected carrier and
forms a generating pair with every escaping natural local member. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_generation
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B ∈ m22Blocks,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
      let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
      (M ⊓ d.L) < H ∧ H < d.L ∧ d.SL ≤ H ∧
      (center d.L).map d.L.subtype ≤ H ∧
      Group.IsPerfect H ∧ generalizedFitting H = pCore 2 H ∧
      H.pCoreIn 2 = ((m22HexadPointwiseKernel B).comap q).map d.L.subtype ∧
      V ⊓ d.L ≤ H.pCoreIn 2 ∧
      Nat.card (pCore 2 H) = 16 * Nat.card (center d.L) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∧
      H.relIndex d.L = 77 ∧ ¬ H ≤ M ∧ ¬ H ≤ d.MZ ∧
      M ⊓ d.G1 ≤ normalizer (H : Set G) ∧ H ∈ Chapter1.LIn d.G1 d.S ∧
      ⁅H,elementaryAbelianMaxJ d.S⁆ = H ∧
      IsCoatom (H.subgroupOf d.L) ∧ ¬ K ≤ H ∧ K ⊔ H = d.L := by
  obtain ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
      hnotM,hnotZ,hCN,hlocal,hmoved⟩ :=
    s.localFamily_linearTwo_m22_full_hexad (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := projection e
  let J := preimage e (MulAction.stabilizer M22 B)
  let H := J.map d.L.subtype
  have hJH : H.subgroupOf d.L = J :=
    comap_map_eq_self_of_injective d.L.subtype_injective J
  have hmax : IsCoatom (H.subgroupOf d.L) := by
    rw [hJH]
    exact isCoatom_comap_of_surjective (projection_surjective e)
      (m22_hexad_stabilizer_isCoatom B hB)
  have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
  have hSN := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  obtain ⟨P,hP⟩ := s.component_sylow
  let Pbar := P.mapSurjective (projection_surjective e)
  let A := (K.subgroupOf d.L).map q
  have hPN : (P : Subgroup d.L) ≤ normalizer (K.subgroupOf d.L : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro x hx k hk
    exact le_normalizer_iff.mp hSN x (hP ▸ mem_map_of_mem d.L.subtype hx).1 k hk
  have hPA : (Pbar : Subgroup M22) ≤ normalizer (A : Set M22) :=
    (map_mono hPN).trans ((K.subgroupOf d.L).le_normalizer_map q)
  have hPH : (Pbar : Subgroup M22) ≤ MulAction.stabilizer M22 B := by
    rintro _ ⟨x,hx,rfl⟩
    have hxH := hSH (hP ▸ mem_map_of_mem d.L.subtype hx)
    have hxJ : x ∈ J := by
      rw [←hJH]
      exact hxH
    exact hxJ
  have hAc : Nat.card A = 960 := by
    change Nat.card ((K.subgroupOf d.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center d.L)))) = 960
    rw [←map_map,card_map_of_injective e.injective]
    exact (s.localFamily_linearTwo_mathieu_image (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).2.2.2.2.2.1
  have hKH : ¬ K ≤ H := by
    intro hh
    apply natural_not_le_hexad Pbar A hPA hAc hB hPH
    apply map_le_iff_le_comap.mpr
    change K.subgroupOf d.L ≤ J
    rw [←hJH]
    exact comap_mono hh
  have hgen : K ⊔ H = d.L := by
    have hsup : K ⊔ H ≤ d.L := sup_le hKL hHL.le
    have hlt : H.subgroupOf d.L < (K ⊔ H).subgroupOf d.L := by
      refine lt_iff_le_not_ge.mpr ⟨comap_mono le_sup_right,?_⟩
      intro hh
      apply hKH
      intro k hk
      exact hh (show (⟨k,hKL hk⟩ : d.L) ∈ (K ⊔ H).subgroupOf d.L from
        (show K ≤ K ⊔ H from le_sup_left) hk)
    have ht := hmax.lt_iff.mp hlt
    have he := congrArg (map d.L.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hsup,←MonoidHom.range_eq_map,range_subtype] using he
  exact ⟨e,B,hB,hMH,hHL,hSH,hZH,hperfect,hfit,hcore,hV,hcard,hmodel,hindex,
    hnotM,hnotZ,hCN,hlocal,hmoved,hmax,hKH,hgen⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the maximal full hexad and its generating
pair with each escaping natural member, with all original markings retained. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_generation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧
          ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B ∈ m22Blocks,
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
            let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
            (M ⊓ d.L) < H ∧ H < d.L ∧ d.SL ≤ H ∧
            (center d.L).map d.L.subtype ≤ H ∧
            Group.IsPerfect H ∧ generalizedFitting H = pCore 2 H ∧
            H.pCoreIn 2 = ((m22HexadPointwiseKernel B).comap q).map d.L.subtype ∧
            V ⊓ d.L ≤ H.pCoreIn 2 ∧
            Nat.card (pCore 2 H) = 16 * Nat.card (center d.L) ∧
            Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) ∧
            H.relIndex d.L = 77 ∧ ¬ H ≤ M ∧ ¬ H ≤ d.MZ ∧
            M ⊓ d.G1 ≤ normalizer (H : Set G) ∧ H ∈ Chapter1.LIn d.G1 d.S ∧
            ⁅H,elementaryAbelianMaxJ d.S⁆ = H ∧
            IsCoatom (H.subgroupOf d.L) ∧ ¬ K ≤ H ∧ K ⊔ H = d.L := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_generation (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
