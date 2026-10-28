module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SylowSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import Theory.GroupAction.RegularComplementBound
public import Theory.GroupTheory.AbelianRegularTorusAction
/-!
# The original torus on the center of the source Sylow subgroup

When the block is centerless, its natural fixed-line bound gives |Z(R)|≤q.
Every nonidentity element of the actual odd torus D has no nontrivial fixed
point in R: apply the proved odd fixed-point lemma to its cyclic subgroup.
The nontrivial two-group center and |D|=q−1 force regularity. Since B is
abelian, its image on Z(R) is exactly the faithful image of D.

All maps are conjugation maps on the original embedded center R∩C_G(R).
Source: Aschbacher–Smith, Lemma 2.4.8(6), printed pp.529–531.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_sylow_center_bound
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    Nat.card (R ⊓ centralizer (R : Set G) : Subgroup G) ≤ 2^n := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  obtain ⟨P,hP⟩ := hf.2.2.1
  change (P : Subgroup L).map L.subtype = R at hP
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hp := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hZU : Z ≤ sourceModule L := hp.ge.trans inf_le_left
  have hZL : Z ≤ L := hZU.trans (map_subtype_le _)
  have heU : Z.subgroupOf L ≤ ChapterC.blockU L := by
    intro z hz
    obtain ⟨u,hu,he⟩ := hZU hz
    exact (Subtype.ext he : u=z) ▸ hu
  have heP : Z.subgroupOf L ≤ centralizer (P : Set L) := by
    intro z hz
    apply mem_centralizer_iff.mpr
    intro p hp
    exact Subtype.ext ((mem_centralizer_iff.mp hz.2) p
      (by rw [← hP]; exact mem_map_of_mem L.subtype hp))
  have hc := hK.card_le_of_sylow_fixed_disjoint_center P (Z.subgroupOf L) heU heP
    (by rw [hZ];exact disjoint_bot_right)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hZL).toEquiv] at hc

theorem source_centerless_odd_fixed_free
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (D : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype) (ho : Odd (Nat.card D)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ a ∈ D, ∀ z ∈ R, z ≠ 1 → a*z*a⁻¹=z → a=1 := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have hRL := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  change ∀ a ∈ D, ∀ z ∈ R, z ≠ 1 → a*z*a⁻¹=z → a=1
  intro a ha z hz hz1 he
  by_contra ha1
  have hcyD : zpowers a ≤ D := zpowers_le.mpr ha
  have hcy : zpowers a ≠ ⊥ := zpowers_ne_bot.mpr ha1
  have hco : Odd (Nat.card (zpowers a)) := ho.of_dvd_nat (card_dvd_of_le hcyD)
  have hzfix : z ∈ centralizer (zpowers a : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hzC := source_odd_fixed_centralizes_block d hG T hST hsingle hL (zpowers a)
    (hcyD.trans hDL) hco hcy ⟨hz,hzfix⟩
  have hzCL : z ∈ centralizer (L : Set G) := centralizer_le
    (show L ≤ L ⊔ R from le_sup_left) hzC
  have hzcenter : (⟨z,hRL hz⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext ((mem_centralizer_iff.mp hzCL) l l.property)
  rw [hZ,mem_bot] at hzcenter
  exact hz1 (congrArg Subtype.val hzcenter)


/-- On the nonidentity center of R the original torus D acts regularly. -/
theorem source_centerless_torus_regular
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (D : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype) (ho : Odd (Nat.card D))
    (hcard : Nat.card D = 2^n-1)
    (hDR : D ≤ normalizer (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    Nat.card Z = 2^n ∧
      ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃! a : D, (a:G)*z*(a:G)⁻¹=w := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  have hDN : D ≤ normalizer (Z : Set G) :=
    (le_inf hDR (hDR.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  let ρ : D →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hDN)
  let : MulDistribMulAction D Z := MulDistribMulAction.compHom Z ρ
  have hfree : ∀ (a : D) (z : Z), z ≠ 1 → a • z = z → a=1 := by
    intro a z hz he
    apply Subtype.ext
    apply source_centerless_odd_fixed_free d hG T hST hsingle hL hM hTM hunique hZ D hDL ho
      a a.property z z.property.1 (fun h => hz (Subtype.ext h))
    exact congrArg Subtype.val he
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hRtwo : IsPGroup 2 R := T.isPGroup'.to_le (hRS.trans hST.le)
  have hQne : twoCore d.H ≠ ⊥ :=
    (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hQle : twoCore d.H ≤ R := le_sSup (d.core_source hG T hST).2.2
  have hRne : R ≠ ⊥ := fun he => hQne (bot_unique (he ▸ hQle))
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot _).mpr hRne
  let : Nontrivial (center R) := hRtwo.center_nontrivial
  obtain ⟨z,hz1⟩ := exists_ne (1 : center R)
  have hzZ : ((z : R) : G) ∈ Z := by
    refine ⟨(z : R).property,mem_centralizer_iff.mpr ?_⟩
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp z.property (⟨r,hr⟩ : R))
  have hne : ∃ z : Z, z ≠ 1 := by
    refine ⟨⟨z,hzZ⟩,?_⟩
    intro he
    have hg : ((z : R) : G) = 1 := congrArg Subtype.val he
    have hr : (z : R) = 1 := Subtype.ext hg
    exact hz1 (Subtype.ext hr)
  have hq : 0 < 2^n := pow_pos (by decide) _
  have hc : Nat.card Z ≤ Nat.card D+1 := by
    rw [hcard,Nat.sub_add_cancel (by omega)]
    exact source_centerless_sylow_center_bound d hG T hST hsingle hL hM hTM hunique hZ
  have he := MulAction.card_eq_of_free_complement_of_le (1 : Z) (fun _ => smul_one _) hfree hc hne
  change Nat.card Z = 2^n ∧ _
  refine ⟨by omega,?_⟩
  intro z hz hz1 w hw hw1
  obtain ⟨a,ha,hu⟩ := MulAction.existsUnique_smul_eq_of_free_complement
    (1 : Z) (fun _ => smul_one _) hfree he
    (show (⟨z,hz⟩ : Z) ≠ 1 from fun h => hz1 (congrArg Subtype.val h))
    (show (⟨w,hw⟩ : Z) ≠ 1 from fun h => hw1 (congrArg Subtype.val h))
  exact ⟨a,congrArg Subtype.val ha,fun b hb => hu b (Subtype.ext hb)⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
/-- The literal torus action in original 2.4.8(6), centerless case. -/
theorem lemma_2_4_8_6b_of_choice
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (D B : Subgroup G) (hDL : D ≤ d.block.map d.H.subtype) (ho : Odd (Nat.card D))
    (hcard : Nat.card D = 2^n-1) (hDB : D ≤ B) [IsMulCommutative B]
    (hBR : B ≤ normalizer (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    ∃ hBZ : B ≤ normalizer (Z : Set G),
      let ρ : B →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hBZ)
      ρ.range = (ρ.comp (inclusion hDB)).range ∧
      Function.Injective (ρ.comp (inclusion hDB)) ∧ Nonempty (D ≃* ρ.range) ∧
      ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 → ∃! a : D, (a:G)*z*(a:G)⁻¹=w := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  have hBZ : B ≤ normalizer (Z : Set G) :=
    (le_inf hBR (hBR.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  let ρ : B →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hBZ)
  let f := ρ.comp (inclusion hDB)
  have hreg := source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hZ
    D hDL ho hcard (hDB.trans hBR)
  change Nat.card Z=2^n ∧ _ at hreg
  have hZn : Z ≠ ⊥ := by
    intro he
    have hc := hreg.1
    rw [he] at hc
    have hn := hL.1
    have hp : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
    have hc' : 1 = 2^n := by simpa using hc
    omega
  obtain ⟨v,hv,hv1⟩ := Z.bot_or_exists_ne_one.resolve_left hZn
  let z : Z := ⟨v,hv⟩
  have hz : z ≠ 1 := fun he => hv1 (congrArg Subtype.val he)
  have htrans (w : Z) (hw : w≠1) : ∃ a : D, ρ (inclusion hDB a) z=w := by
    obtain ⟨a,ha,_⟩ := hreg.2 v hv hv1 w w.property (fun he => hw (Subtype.ext he))
    exact ⟨a,Subtype.ext ha⟩
  have hr := abelian_action_range_eq_of_regular_subgroup B D hDB ρ z hz htrans
  have hi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    have he : f a z=z := by change f a=1 at ha;rw [ha];rfl
    exact source_centerless_odd_fixed_free d hG T hST hsingle hL hM hTM hunique hZ D hDL ho
      a a.property v hv.1 hv1 (congrArg Subtype.val he)
  refine ⟨hBZ,hr,hi,?_,hreg.2⟩
  exact ⟨(MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr.symm)⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
