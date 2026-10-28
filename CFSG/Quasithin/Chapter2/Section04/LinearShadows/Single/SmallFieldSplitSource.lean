module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SmallFieldGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OddComplementSource
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Mathlib.GroupTheory.NoncommCoprod
/-!
# The original degree-two field-centralizer splitting

The field complement has order dividing two and contains the marked involution,
so it is precisely its cyclic subgroup. The original Hall-normalizer split then
writes the field centralizer as a product of the core fixed group with that
complement. The source outside split involution gives a complementary factor,
and multiplication realizes the central involution as a direct factor.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, printed p.539.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
omit [Finite G] in
private theorem powers_two_cases (w:G) (hw:orderOf w=2) {a:G} (ha:a∈zpowers w) : a=1 ∨ a=w := by
  classical
  have hp : w^2=1 := by simpa only [hw] using pow_orderOf_eq_one w
  have hf : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hp⟩
  rw [hf.mem_zpowers_iff_mem_range_orderOf,hw] at ha
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ha
  have hj2 := Finset.mem_range.mp hj
  have hh : j=0 ∨ j=1 := by omega
  rcases hh with rfl|rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)
theorem source_centerless_small_field_centralizer_split
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) (hL : ChapterC.IsL2EvenBlock d.block 2)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T 2) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s:T) (hs:(s:G)∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2:orderOf s=2)
    (hsR:(s:G)∉Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)) :
    let S := (d.S:Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let P := R⊓centralizer ({(s:G)}:Set G)
    let Ts := (T:Subgroup G)⊓centralizer ({(s:G)}:Set G)
    ∃ x∈T, x∉S ∧ orderOf x=2 ∧ x∈centralizer ({(s:G)}:Set G) ∧
      Nonempty (Ts ≃* Multiplicative (ZMod 2) × (P⊔zpowers x : Subgroup G)) := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := centralizer ({(s:G)}:Set G)
  let P := R⊓C
  let Ts := (T:Subgroup G)⊓C
  let F := S⊓normalizer (c.hall:Set G)
  let TB := (T:Subgroup G)⊓normalizer (c.hall:Set G)
  have hRS : R≤S := sSup_le fun _ h=>h.1
  have hRT : R≤(T:Subgroup G) := hRS.trans hST.le
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hFd : Nat.card F∣2 := source_field_complement_card_dvd_degree d hG T hST hsingle hL hM hTM hu c
  have hF : F=zpowers (s:G) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hs) ?_).symm
    rw [Nat.card_zpowers,hsord]
    exact Nat.le_of_dvd (by decide) hFd
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  obtain ⟨x,hx,hxS,hx2,_,_,hxf,hTB⟩ := source_centerless_split_involution d hG T hST hsingle hL hM hTM hu c hZ hclosed
  change TB=zpowers x⊔F at hTB
  have hxs : x∈C := mem_centralizer_singleton_iff.mpr (hxf s hs)
  have hTBC : TB≤C := by
    rw [hTB,hF]
    exact sup_le (zpowers_le.mpr hxs) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hsplit : P⊔TB=Ts := by
    apply le_antisymm (sup_le (le_inf (inf_le_left.trans hRT) inf_le_right) (le_inf inf_le_left hTBC))
    intro a ha
    obtain ⟨⟨r,b⟩,he⟩ := c.split_ambient.2 (⟨a,ha.1⟩:T)
    have hb : ((b:T):G)∈TB := ⟨(b:T).property,b.property⟩
    have heG : ((r:T):G)*((b:T):G)=a := congrArg Subtype.val he
    have hrC : ((r:T):G)∈C := by
      have hh := C.mul_mem ha.2 (C.inv_mem (hTBC hb))
      rw [←heG] at hh
      simpa only [mul_inv_cancel_right] using hh
    rw [←heG]
    exact mul_mem_sup ⟨r.property,hrC⟩ hb
  let J := P⊔zpowers x
  have hJTs : J≤Ts := sup_le (le_inf (inf_le_left.trans hRT) inf_le_right) (zpowers_le.mpr ⟨hx.1,hxs⟩)
  have hTR : (T:Subgroup G)≤normalizer (R:Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp c.normal_in_sylow
  have hxn : x∈normalizer (P:Set G) := inf_normalizer_le_normalizer_inf ⟨hTR hx.1,C.le_normalizer hxs⟩
  have hsJ : (s:G)∉J := by
    intro hsJ
    have hh : (s:G)∈(P:Set G)*(zpowers x:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left P (zpowers x) (zpowers_le.mpr hxn)]
      exact hsJ
    obtain ⟨r,hr,b,hb,he⟩ := hh
    rcases powers_two_cases x hx2 hb with hb1|hbx
    · have her : r=(s:G) := by simpa only [hb1,mul_one] using he
      have hsP : (s:G)∈P := her ▸ hr
      exact hsR hsP.1
    · apply hxS
      have hxe : x=r⁻¹*(s:G) := by
        rw [hbx] at he
        rw [←he]
        simp only [inv_mul_cancel_left]
      rw [hxe]
      exact S.mul_mem (S.inv_mem (hRS hr.1)) hs.1
  have hgen : zpowers (s:G)⊔J=Ts := by
    change zpowers (s:G)⊔(P⊔zpowers x)=Ts
    rw [←hsplit,hTB,hF]
    ac_rfl
  have hdisj : Disjoint (zpowers (s:G)) J :=
    (J.disjoint_zpowers_of_prime_order_not_mem (s:G) hsord hsJ).symm
  have hcomm (a:zpowers (s:G)) (b:J) : Commute (a:G) (b:G) := by
    have hCJ : zpowers (s:G)≤centralizer (J:Set G) := by
      apply zpowers_le.mpr
      intro j hj
      exact mem_centralizer_singleton_iff.mp ((hJTs hj).2)
    exact (hCJ a.property b b.property).symm
  let f : zpowers (s:G) × J →* G := (zpowers (s:G)).subtype.noncommCoprod J.subtype hcomm
  have hf : Function.Injective f := mul_injective_of_disjoint hdisj
  have hrange : f.range=Ts := by
    exact (MonoidHom.noncommCoprod_range (zpowers (s:G)).subtype J.subtype hcomm).trans
      (by simpa only [range_subtype] using hgen)
  let e := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  let es : zpowers (s:G) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq ((Nat.card_zpowers _).trans hsord) (by simp)
  exact ⟨x,hx.1,hxS,hx2,hxs,⟨e.symm.trans (MulEquiv.prodCongr es (MulEquiv.refl J))⟩⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
