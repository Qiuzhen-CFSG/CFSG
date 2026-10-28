module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CentralizerStructure
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourCentralizerGeneration
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Unique involution in the paired-cubic component centralizer

Normality of the selected A₆ in each relevant involution centralizer forces
uniqueness of the original involution in C_R(K). A second involution would
give a four-group. Conjugating it puts an inner involution in the full A₆
automorphism action; its involution centralizers generate the whole local
group. Thus K and its exchanged conjugate normalize one another. Distinct
copies would commute, violating quasithin local three-rank, while equality
would put the original central involution in the center of A₆.

The final application supplies the cyclic-four centralizer and the actual
dihedral factor decomposition used by the terminal count. The first paragraph
of source 2.4.36, normality in each involution centralizer, and source 2.4.37
fusion remain explicit inputs with separate original-source producers.
Source: Aschbacher–Smith, 2.4.36, printed pp.549–550.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem a6_mutually_normalizing_eq (hG : IsQuasithin G)
    (K L : Subgroup G) (eK : K ≃* A6) (eL : L ≃* A6)
    (hKL : K ≤ normalizer (L : Set G)) (hLK : L ≤ normalizer (K : Set G)) : K = L := by
  let J := K ⊔ L
  let K₀ := K.subgroupOf J
  let L₀ := L.subgroupOf J
  let ek : K₀ ≃* A6 := (subgroupOfEquivOfLe le_sup_left).trans eK
  let el : L₀ ≃* A6 := (subgroupOfEquivOfLe le_sup_right).trans eL
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K₀ := ek.isSimpleGroup
  let : IsSimpleGroup L₀ := el.isSimpleGroup
  let : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect K₀ := Group.IsPerfect.ofSurjective (f := ek.symm.toMonoidHom) ek.symm.surjective
  let : Group.IsPerfect L₀ := Group.IsPerfect.ofSurjective (f := el.symm.toMonoidHom) el.symm.surjective
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hLK)
  let : L₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le hKL L.le_normalizer)
  by_contra hne
  have hne₀ : K₀ ≠ L₀ := by
    intro hh
    have hm := congrArg (Subgroup.map J.subtype) hh
    rw [map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right] at hm
    exact hne hm
  have hc₀ := simple_subnormal_commute_of_ne K₀ L₀
    (inferInstance : K₀.Normal).isSubnormal (inferInstance : L₀.Normal).isSubnormal hne₀
  have hc : K ≤ centralizer (L : Set G) := by
    intro k hk l hl
    exact congrArg Subtype.val (commutator_eq_bot_iff_le_centralizer.mp hc₀
      (show (⟨k,mem_sup_left hk⟩ : J) ∈ K₀ from hk) ⟨l,mem_sup_right hl⟩ hl)
  exact alternatingGroup.not_commuting_a6_of_quasithin hG K L eK eL hc

/-- The source centralizer-normality conclusion excludes an elementary four
inside the actual component centralizer containing the original involution. -/
theorem SourceComponentGeometry.not_four_in_component_centralizer
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hG : IsQuasithin G)
    (hs2 : c.s ^ 2 ∈ involutionCentralizer c.z)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hER : E ≤ sourceR d)
    (hEC : E ≤ centralizer (c.K.map (involutionCentralizer c.z).subtype : Set G))
    (hzE : c.z ∈ E)
    (hn : ∀ r : involutionCentralizer c.z,
      r ∈ (sourceR d).subgroupOf (involutionCentralizer c.z) →
      r ∈ centralizer (c.K : Set (involutionCentralizer c.z)) → orderOf r = 2 →
      centralizer ({(r:G)} : Set G) ≤
        normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G)) : False := by
  let H := involutionCentralizer c.z
  let K := c.K.map H.subtype
  let e := MulAut.conj c.s
  let E₁ := E.map e.toMonoidHom
  let N := normalizer (K : Set G)
  have hez : e c.z = (c.z₁ : G) := by
    apply (MulAut.conj c.s⁻¹).injective
    simpa only [e,MulAut.conj_apply,inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one]
      using c.exchange.symm
  have hez₁ : e (c.z₁ : G) = c.z := by
    rw [←hez]
    change c.s * (c.s * c.z * c.s⁻¹) * c.s⁻¹ = c.z
    have hh := mem_centralizer_singleton_iff.mp hs2
    change c.s^2*c.z = c.z*c.s^2 at hh
    calc
      _ = c.s^2*c.z*(c.s^2)⁻¹ := by simp only [pow_two]; group
      _ = c.z := mul_inv_eq_iff_eq_mul.mpr hh
  have hE₁H : E₁ ≤ H := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := hEC ha (c.z₁ : G) (mem_map_of_mem H.subtype c.first_in_component)
    have hm := congrArg e hh
    change e a * c.z = c.z * e a
    simpa only [map_mul,hez₁] using hm.symm
  let D := E₁.subgroupOf H
  let : IsElementaryAbelian 2 E₁ := IsElementaryAbelian.map e.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hE₁H
  have hD : Nat.card D = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hE₁H).toEquiv,card_map_of_injective e.injective,hE]
  let N₁ := (N.map e.toMonoidHom).subgroupOf H
  have hzD : c.z₁ ∈ D := by
    change (c.z₁:G) ∈ E₁
    rw [←hez]
    exact mem_map_of_mem e.toMonoidHom hzE
  have hz₁ : orderOf (⟨c.z₁,c.first_in_component⟩ : c.K) = 2 := by
    have hzo : orderOf c.z = 2 := orderOf_eq_prime c.involution c.nonidentity
    rw [←orderOf_coe,←orderOf_coe,←hez,e.orderOf_eq,hzo]
  have hfull : N₁ = ⊤ := eq_top_of_four_involution_centralizers c.K c.componentEquiv
    (conjugation_surjective_of_source_outer_actions c.K c.componentEquiv c.u c.x c.σ
      c.swap c.transposition c.outside_natural) D hD ⟨c.z₁,c.first_in_component⟩ hz₁ hzD N₁ (by
        intro a ha hao b hb
        obtain ⟨r,hr,he⟩ := ha
        change e r = (a:G) at he
        have hrH : r ∈ H := c.thompson_le (hER hr)
        let rH : H := ⟨r,hrH⟩
        have hrc : rH ∈ centralizer (c.K : Set H) := by
          intro k hk
          exact Subtype.ext (hEC hr k (mem_map_of_mem H.subtype hk))
        have hro : orderOf rH = 2 := by
          rw [←orderOf_coe,←e.orderOf_eq r,he,orderOf_coe,hao]
        have hbC : e.symm (b : G) ∈ centralizer ({r} : Set G) := by
          apply mem_centralizer_singleton_iff.mpr
          apply e.injective
          simp only [map_mul,e.apply_symm_apply,he]
          exact congrArg H.subtype (mem_centralizer_singleton_iff.mp hb)
        exact ⟨e.symm (b:G),hn rH (hER hr) hrc hro hbC,e.apply_symm_apply _⟩)
  have hHN : H ≤ N.map e.toMonoidHom := subgroupOf_eq_top.mp hfull
  have hHK : H ≤ normalizer (K : Set G) := by
    have hh := c.K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,H.range_subtype] at hh
  have heK2 : (K.map e.toMonoidHom).map e.toMonoidHom = K := by
    rw [map_map]
    have hhom : e.toMonoidHom.comp e.toMonoidHom = (MulAut.conj (c.s^2)).toMonoidHom := by
      ext g
      change c.s*(c.s*g*c.s⁻¹)*c.s⁻¹ = c.s^2*g*(c.s^2)⁻¹
      simp only [pow_two]
      group
    rw [hhom]
    exact mem_normalizer_iff_map_conj_eq.mp (hHK hs2)
  let K₁ := K.map e.toMonoidHom
  have hKK₁ : K ≤ normalizer (K₁ : Set G) := by
    have hh := (map_subtype_le c.K).trans hHN
    rwa [map_equiv_normalizer_eq] at hh
  have hK₁K : K₁ ≤ normalizer (K : Set G) := by
    have hh := map_mono (f := e.toMonoidHom) hKK₁
    rw [map_equiv_normalizer_eq,heK2] at hh
    exact hh
  let eK : K ≃* A6 := (c.K.equivMapOfInjective H.subtype H.subtype_injective).symm.trans c.componentEquiv
  have heq : K = K₁ := a6_mutually_normalizing_eq hG K K₁ eK ((e.subgroupMap K).symm.trans eK) hKK₁ hK₁K
  have hzK : c.z ∈ K := by
    rw [heq]
    exact hez₁ ▸ mem_map_of_mem e.toMonoidHom (mem_map_of_mem H.subtype c.first_in_component)
  obtain ⟨k,hk,hkg⟩ := hzK
  change (k:G) = c.z at hkg
  have hzcent : (⟨k,hk⟩ : c.K) ∈ center c.K := by
    rw [mem_center_iff]
    intro a
    apply Subtype.ext
    apply Subtype.ext
    change (a.val:G)*(k:G)=(k:G)*(a.val:G)
    rw [hkg]
    exact mem_centralizer_singleton_iff.mp a.val.property
  have hzbot := (centerCongr c.componentEquiv ⟨⟨k,hk⟩,hzcent⟩).property
  change c.componentEquiv ⟨k,hk⟩ ∈ center A6 at hzbot
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hzbot
  have hk1 : (⟨k,hk⟩ : c.K) = 1 := c.componentEquiv.map_eq_one_iff.mp hzbot
  exact c.nonidentity (hkg.symm.trans (congrArg (fun a : c.K => ((a:H):G)) hk1))


/-- The original central involution is unique in C_R(K), once the earlier
source36 normality in each involution centralizer has been constructed. -/
theorem SourceComponentGeometry.unique_component_centralizer_involution
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hG : IsQuasithin G)
    (hzR : c.z ∈ sourceR d)
    (hs2 : c.s ^ 2 ∈ involutionCentralizer c.z)
    (hn : ∀ r : involutionCentralizer c.z,
      r ∈ (sourceR d).subgroupOf (involutionCentralizer c.z) →
      r ∈ centralizer (c.K : Set (involutionCentralizer c.z)) → orderOf r = 2 →
      centralizer ({(r:G)} : Set G) ≤
        normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G)) :
    ∃! z : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (c.K : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)),
      orderOf z = 2 := by
  classical
  let H := involutionCentralizer c.z
  let B := (sourceR d).subgroupOf H ⊓ centralizer (c.K : Set H)
  let zH : H := ⟨c.z,mem_centralizer_singleton_iff.mpr rfl⟩
  have hzB : zH ∈ B := by
    refine ⟨hzR,?_⟩
    intro k hk
    exact Subtype.ext (mem_centralizer_singleton_iff.mp k.property)
  let zB : B := ⟨zH,hzB⟩
  have hzo : orderOf c.z = 2 := orderOf_eq_prime c.involution c.nonidentity
  refine ⟨zB,?_,?_⟩
  · change orderOf zB = 2
    rw [←orderOf_coe,←orderOf_coe]
    exact hzo
  intro r hro
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  let rG : G := r.val.val
  have hr2 : rG ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one r
    rw [hro] at hh
    exact congrArg (fun b : B => ((b:H):G)) hh
  have hr1 : rG ≠ 1 := by
    intro hh
    have he : r=1 := Subtype.ext (Subtype.ext hh)
    simp only [he,orderOf_one] at hro
    omega
  have hcomm : Commute c.z rG := (mem_centralizer_singleton_iff.mp r.val.property).symm
  let E := zpowers c.z ⊔ zpowers rG
  have hrc : rG ∈ centralizer (zpowers c.z : Set G) := by
    intro a ha
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
    exact (hcomm.zpow_left n).eq
  let : IsElementaryAbelian 2 (zpowers c.z) := IsElementaryAbelian.zpowers_of_pow_eq_one c.involution
  let : IsElementaryAbelian 2 (zpowers rG) := IsElementaryAbelian.zpowers_of_pow_eq_one hr2
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hrc)
  have hrout : rG ∉ zpowers c.z := by
    intro hh
    rw [mem_zpowers_iff_mem_range_orderOf,hzo] at hh
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact hr1 (by simpa using he.symm)
    · exact hne (by simpa only [pow_one] using he.symm)
  have hE : Nat.card E = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers c.z) rG hr2 hrout
      (Subgroup.centralizer_le_normalizer _ hrc),Nat.card_zpowers,hzo]
  have hER : E ≤ sourceR d := sup_le (zpowers_le.mpr hzR) (zpowers_le.mpr r.property.1)
  have hEC : E ≤ centralizer (c.K.map H.subtype : Set G) := by
    apply sup_le <;> apply zpowers_le.mpr
    · rintro _ ⟨k,hk,rfl⟩
      exact mem_centralizer_singleton_iff.mp k.property
    · rintro _ ⟨k,hk,rfl⟩
      exact congrArg Subtype.val (r.property.2 k hk)
  exact c.not_four_in_component_centralizer hG hs2 E hE hER hEC
    (mem_sup_left (mem_zpowers _)) hn

/-- Literal source36-to-terminal application: only the independently owned
normality, original source30 coordinates, and source37 fusion remain. -/
theorem SourceComponentGeometry.false_of_involution_centralizer_normality
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hG : IsQuasithin G) (hzR : c.z ∈ sourceR d)
    (hs2 : c.s ^ 2 ∈ involutionCentralizer c.z)
    (hn : ∀ r : involutionCentralizer c.z,
      r ∈ (sourceR d).subgroupOf (involutionCentralizer c.z) →
      r ∈ centralizer (c.K : Set (involutionCentralizer c.z)) → orderOf r = 2 →
      centralizer ({(r:G)} : Set G) ≤
        normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G))
    (hi : (((sourceR d).subgroupOf (involutionCentralizer c.z)).subgroupOf
      (c.S₁ : Subgroup (involutionCentralizer c.z))).index = 2)
    (hx : c.x ∈ (c.S₁ : Subgroup (involutionCentralizer c.z)))
    (hodd : pPrimeCore 2 (involutionCentralizer c.z) = ⊥)
    (L : Subgroup (involutionCentralizer c.z)) (hLK : L ≤ c.K)
    (eL : L ≃* alternatingGroup (Fin 4))
    (huR : c.u ∈ (sourceR d).subgroupOf (involutionCentralizer c.z))
    (huL : c.u ∈ centralizer (L : Set (involutionCentralizer c.z)))
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (eC : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓
      centralizer (L : Set (involutionCentralizer c.z)) : Subgroup (involutionCentralizer c.z)) ≃*
        (E × DihedralGroup 4))
    (hR : Nat.card (sourceR d) = Nat.card E * 64)
    (hsR : c.s ∈ normalizer (sourceR d : Set G))
    (hsK : c.s^2 ∈ normalizer (c.K.map (involutionCentralizer c.z).subtype : Set G))
    (hz₁R : (c.z₁:G) ∈ centralizer (sourceR d : Set G))
    (hf : SourceElementarySixteenFusion c) : False :=
  c.false_of_unique_centralizer_involution hi hx hodd L hLK eL huR huL eC hR
    (c.unique_component_centralizer_involution hG hzR hs2 hn) hsR hsK hz₁R hf

end CFSG.Quasithin.Chapter2.DoubleA3
