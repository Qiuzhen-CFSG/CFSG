module
public import Theory.SpecificGroups.PSL2.TorusFixedInner
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource

/-!
# The source kernel on the distinguished elementary subgroup

For the selected complement F = N_S(B), pointwise fixation of D forces its
quotient actor on L/O₂(L) to be inner. The original action kernel lies in L,
so the splitting H = LF makes C_F(D) trivial.

If the block is centerless, D acts faithfully on Z(R). An element of F
centralizing Z(R) therefore centralizes D. If the block center is nontrivial,
Dˣ acts faithfully on Z(L); conjugating by the original outside element x
preserves F because S has index two in T, and reduces to the same argument.
The split product S = RF now gives C_S(Z) = R in both branches of the
literal distinguished subgroup of Notation 2.4.15.

Source: Aschbacher–Smith, Lemma 2.4.17(1), printed p.534, using the original
2.4.8 torus actions and 2.4.12 splitting. The final wrapper constructs all
torus and quotient markings; no field-action or innerness premise remains.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The selected complement has no nonidentity element centralizing the original torus. -/
theorem source_torus_normalizer_centralizer_eq_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) :
    ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G)) ⊓
      centralizer (c.torus : Set G) = ⊥ := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let A := (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G)
  let K := d.block ⧸ pCore 2 d.block
  let iL := d.H.subtype.comp d.block.subtype
  let iA := inclusion (show A ≤ d.H from inf_le_left.trans (map_subtype_le _))
  let ρ := (normalQuotientAction d.block (pCore 2 d.block)).comp iA
  obtain ⟨F,_,_,_,hF,e,P,D,hP,hD,hDN,_,hgen,hact⟩ :=
    source_field_actor_borel_of_choice d hG T hST hsingle hL hM hTM hunique
      c.torus c.hall c.torus_le c.torus_le_hall c.hall_odd c.torus_card c.sylow_normalizes_borel
  have hker : (normalQuotientAction d.block (pCore 2 d.block)).ker ≤ d.block := by
    apply (source_block_quotient_action_kernel d hsingle hL).trans
    intro a ha
    have hcore := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
    have ha' : (a:G) ∈ (d.block.map d.H.subtype).pCoreIn 2 := by
      change (a:G) ∈ twoCore (d.block.map d.H.subtype)
      rw [hcore]
      exact mem_map_of_mem d.H.subtype ha
    exact (mem_map_iff_mem d.H.subtype_injective).mp (pCoreIn_le 2 _ ha')
  apply eq_bot_iff.mpr
  rintro a ⟨ha,hac⟩
  let aA : A := ⟨a,ha⟩
  have hfixed : ∀ x ∈ D, ρ aA x = x := by
    intro x hx
    rw [hD] at hx
    obtain ⟨l,hl,rfl⟩ := hx
    change normalQuotientAction d.block (pCore 2 d.block) (iA aA)
      (QuotientGroup.mk' (pCore 2 d.block) l) = _
    rw [normalQuotientAction_apply_mk]
    congr 1
    apply d.H.subtype_injective.comp d.block.subtype_injective
    change a * iL l * a⁻¹ = iL l
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hac) (iL l) hl).symm
  have hi : ρ aA ∈ MulAut.innerSubgroup K :=
    Matrix.ProjectiveSpecialLinearGroup.inner_of_torus_fixed F e P D (ρ aA)
      hDN hgen (hact aA).1 hfixed
  have haL : iA aA ∈ d.block := by
    have hh : iA aA ∈ (MulAut.innerSubgroup K).comap
        (normalQuotientAction d.block (pCore 2 d.block)) := hi
    rwa [normalQuotientAction_comap_inner, sup_eq_left.mpr hker] at hh
  have hd := (source_torus_normalizer_complements_of_choice d hG T hST hsingle hL
    hM hTM hunique c.hall c.split_ambient).2.2.2.1
  exact disjoint_def.mp hd (mem_map_of_mem d.H.subtype haL) ha

omit [Finite G] in
private theorem centralizes_faithful_normalized_torus
    (D Z : Subgroup G) (hDZ : D ≤ normalizer (Z : Set G))
    (hfaith : D ⊓ centralizer (Z : Set G) = ⊥)
    {f : G} (hfD : f ∈ normalizer (D : Set G)) (hfZ : f ∈ centralizer (Z : Set G)) :
    f ∈ centralizer (D : Set G) := by
  apply mem_centralizer_iff.mpr
  intro d hd
  have hcD : f*d*f⁻¹*d⁻¹ ∈ D := D.mul_mem
    ((mem_normalizer_iff.mp hfD d).mp hd) (D.inv_mem hd)
  have hcZ : f*d*f⁻¹*d⁻¹ ∈ centralizer (Z : Set G) := by
    have hn := normalizer_le_normalizer_centralizer Z (hDZ hd)
    have hh := (mem_normalizer_iff.mp hn f⁻¹).mp ((centralizer (Z : Set G)).inv_mem hfZ)
    simpa only [mul_assoc] using (centralizer (Z : Set G)).mul_mem hfZ hh
  have he : f*d*f⁻¹*d⁻¹ = 1 := mem_bot.mp (hfaith ▸ (show _ ∈ D ⊓ centralizer (Z : Set G) from ⟨hcD,hcZ⟩))
  have hh : f*d*f⁻¹=d := mul_inv_eq_one.mp he
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Original 2.4.17: in the centerless case the kernel on Z(R) inside S is exactly R. -/
theorem source_centerless_sylow_centralizer_eq
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R : Set G)
  let A := S ⊓ normalizer (c.hall : Set G)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hDZ : c.torus ≤ normalizer (Z : Set G) :=
    (le_inf (c.torus_le_hall.trans c.hall_normalizes)
      ((c.torus_le_hall.trans c.hall_normalizes).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hr := source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hz
    c.torus (c.torus_le.trans inf_le_right)
    (c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall)) c.torus_card
    (c.torus_le_hall.trans c.hall_normalizes)
  have hZn : Z ≠ ⊥ := by
    intro he
    have hh := hr.1
    change Nat.card Z = 2^n at hh
    rw [he] at hh
    have hp : 1 < 2^n := Nat.one_lt_pow (by have := hL.1; omega) (by decide)
    have hh' : 1=2^n := by simpa using hh
    omega
  obtain ⟨z,hzZ,hz1⟩ := Z.bot_or_exists_ne_one.resolve_left hZn
  have hf : c.torus ⊓ centralizer (Z : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro a ⟨ha,hac⟩
    exact source_centerless_odd_fixed_free d hG T hST hsingle hL hM hTM hunique hz
      c.torus (c.torus_le.trans inf_le_right)
      (c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall)) a ha z hzZ.1 hz1
      (mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hac) z hzZ).symm)
  have hAD : A ≤ normalizer (c.torus : Set G) := torusNormalizer_preserves_borel_complement
    S R c.torus c.hall (T.isPGroup'.to_le (hRS.trans hST.le)) c.hall_odd
    c.torus_le_hall (c.torus_le_hall.trans c.hall_normalizes) c.sylow_normalizes_borel
  have hAC : A ⊓ centralizer (Z : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro f ⟨hfA,hfZ⟩
    have hfc := centralizes_faithful_normalized_torus c.torus Z hDZ hf (hAD hfA) hfZ
    exact (source_torus_normalizer_centralizer_eq_bot d hG T hST hsingle hL hM hTM hunique c) ▸
      (show f ∈ A ⊓ centralizer (c.torus : Set G) from ⟨hfA,hfc⟩)
  have hRC : R ≤ centralizer (Z : Set G) := le_centralizer_iff.mpr inf_le_right
  rw [distinguishedZ_of_centerless d hz]
  apply le_antisymm _ (le_inf hRS hRC)
  rintro s ⟨hs,hsc⟩
  obtain ⟨⟨r,f⟩,he⟩ := c.split_sylow.2 (⟨s,hs⟩ : S)
  have heG := congrArg Subtype.val he
  change ((r:S):G)*((f:S):G)=s at heG
  have hfC : ((f:S):G) ∈ centralizer (Z : Set G) := by
    have hh : ((f:S):G)=((r:S):G)⁻¹*s := by rw [←heG,inv_mul_cancel_left]
    rw [hh]
    exact (centralizer (Z : Set G)).mul_mem ((centralizer (Z : Set G)).inv_mem (hRC r.property)) hsc
  have hf1 : ((f:S):G)=1 := mem_bot.mp (hAC ▸ (show ((f:S):G) ∈ A ⊓ centralizer (Z : Set G) from ⟨f.property,hfC⟩))
  rw [hf1,mul_one] at heG
  exact heG ▸ r.property

/-- Original 2.4.17 kernel in the nontrivial-center branch. -/
theorem source_noncenterless_sylow_centralizer_eq
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let L := d.block.map d.H.subtype
  let Z := (center L).map L.subtype
  let A := S ⊓ normalizer (c.hall : Set G)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hAD : A ≤ normalizer (c.torus : Set G) := torusNormalizer_preserves_borel_complement
    S R c.torus c.hall (T.isPGroup'.to_le (hRS.trans hST.le)) c.hall_odd
    c.torus_le_hall (c.torus_le_hall.trans c.hall_normalizes) c.sylow_normalizes_borel
  obtain ⟨x,hxT,hxS,hxB⟩ := c.outside
  let E := c.torus.map (MulAut.conj x⁻¹).toMonoidHom
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle hK).1
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp (normal_of_index_eq_two hindex)
  have hxA : x ∈ normalizer (A : Set G) := inf_normalizer_le_normalizer_inf
    ⟨hTS hxT, (normalizer (c.hall : Set G)).le_normalizer hxB⟩
  have hxinvA : x⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hxA
  have hAE : A ≤ normalizer (E : Set G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp hxinvA]
    exact (map_mono hAD).trans (c.torus.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  have hEL := (source_conjugate_torus_normalizes_block d hG T hST hsingle hL hM hTM hunique
    c.torus (c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall))
    (c.torus_le_hall.trans c.hall_normalizes) x hxT hxS).2.2
  have hr := (source_center_torus_of_choice d hG T hST hsingle hL hM hTM hunique
    c.torus c.hall x hxT (c.torus_le.trans inf_le_right)
    (c.hall_odd.of_dvd_nat (card_dvd_of_le c.torus_le_hall)) c.torus_card
    (c.conjugate_pair x hxT hxS hxB) c.hall_fixed hEL).resolve_left hz
  have hZn : Z ≠ ⊥ := fun he => hz
    ((map_injective L.subtype_injective) (he.trans (Subgroup.map_bot _).symm))
  obtain ⟨z,hzZ,hz1⟩ := Z.bot_or_exists_ne_one.resolve_left hZn
  have hf : E ⊓ centralizer (Z : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro a ⟨ha,hac⟩
    have hz1' : (⟨z,hzZ⟩ : Z) ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    obtain ⟨b,hb,hu⟩ := hr.2.2 ⟨z,hzZ⟩ hz1' ⟨z,hzZ⟩ hz1'
    have hh : a*z*a⁻¹=z := mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hac) z hzZ).symm
    have hone : ((1:E):G)*z*((1:E):G)⁻¹=z := by simp
    exact congrArg Subtype.val ((hu ⟨a,ha⟩ hh).trans (hu 1 hone).symm)
  have hAC : A ⊓ centralizer (Z : Set G) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro f ⟨hfA,hfZ⟩
    have hfc := centralizes_faithful_normalized_torus E Z hr.2.1 hf (hAE hfA) hfZ
    have hxfA : x*f*x⁻¹ ∈ A := (mem_normalizer_iff.mp hxA f).mp hfA
    have hxfC : x*f*x⁻¹ ∈ centralizer (c.torus : Set G) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      have he : x⁻¹*a*x ∈ E := by
        simpa only [E, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
          using mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom ha
      have hh := (mem_centralizer_iff.mp hfc) (x⁻¹*a*x) he
      have hh' := congrArg (fun y : G => x*y*x⁻¹) hh
      calc
        a * (x*f*x⁻¹) = x*((x⁻¹*a*x)*f)*x⁻¹ := by group
        _ = x*(f*(x⁻¹*a*x))*x⁻¹ := hh'
        _ = (x*f*x⁻¹)*a := by group
    have hxf1 : x*f*x⁻¹=1 := mem_bot.mp
      ((source_torus_normalizer_centralizer_eq_bot d hG T hST hsingle hL hM hTM hunique c) ▸
        (show x*f*x⁻¹ ∈ A ⊓ centralizer (c.torus : Set G) from ⟨hxfA,hxfC⟩))
    have hh : (MulAut.conj x) f = (MulAut.conj x) 1 := by simpa using hxf1
    exact (MulAut.conj x).injective hh
  have hRC : R ≤ centralizer (Z : Set G) := by
    have hZ := (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.2.1
    rw [distinguishedZ_of_center_ne_bot d hz] at hZ
    exact le_centralizer_iff.mpr (hZ.trans inf_le_right)
  rw [distinguishedZ_of_center_ne_bot d hz]
  apply le_antisymm _ (le_inf hRS hRC)
  rintro s ⟨hs,hsc⟩
  obtain ⟨⟨r,f⟩,he⟩ := c.split_sylow.2 (⟨s,hs⟩ : S)
  have heG := congrArg Subtype.val he
  change ((r:S):G)*((f:S):G)=s at heG
  have hfC : ((f:S):G) ∈ centralizer (Z : Set G) := by
    have hh : ((f:S):G)=((r:S):G)⁻¹*s := by rw [←heG,inv_mul_cancel_left]
    rw [hh]
    exact (centralizer (Z : Set G)).mul_mem ((centralizer (Z : Set G)).inv_mem (hRC r.property)) hsc
  have hf1 : ((f:S):G)=1 := mem_bot.mp (hAC ▸ (show ((f:S):G) ∈ A ⊓ centralizer (Z : Set G) from ⟨f.property,hfC⟩))
  rw [hf1,mul_one] at heG
  exact heG ▸ r.property

/-- The actual distinguished subgroup of 2.4.15 has centralizer R inside S.
The original source constructs all torus and quotient-action data internally. -/
theorem source_distinguished_sylow_centralizer_eq
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    (d.S : Subgroup d.H).map d.H.subtype ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨c⟩ := source_cyclic_torus_setup d hG T hST hsingle hL hM hTM hunique
  by_cases hz : center (d.block.map d.H.subtype) = ⊥
  · exact source_centerless_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique c hz
  · exact source_noncenterless_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique c hz
end CFSG.Quasithin.Chapter2.LinearShadows.Single
