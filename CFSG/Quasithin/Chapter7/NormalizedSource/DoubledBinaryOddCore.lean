module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
-- Internal companion: reduce the original plane and its literal fixer without
-- exposing their implementations through the public boundary.
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.ElementaryAbelian.Injective
/-!
# Odd-core elimination for the binary paired-plane overgroup

A cubic fixing a paired plane has exactly that plane as its fixed space.
Transporting its norm decomposition through the original component action
proves W = U[W,L₀], where L₀ = O²(C_L(U)). The residual action on
[W,L₀] is idempotent. Source A.1.26 therefore makes this commutator
centralize the odd core of any strongly quasithin overgroup H containing
W and L₀. When H centralizes U, its odd core centralizes all of W.

The characteristic-two intersection H∩M then kills that odd core. The
chosen-module application in NonFFSourceDoubledBinaryOddCore supplies all
premises for the actual Sylow-placed plane and minimal escaping H.
Component elimination and ambient containment remain with the final owner
qt-d-1222-nonff-doubled; trivial odd core alone is not characteristic two.
Source: Aschbacher–Smith, 7.7.6 proof, printed pp.704–705, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree NaturalDual
open CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
open CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
open CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore
private def cubic : Group := ⟨!![1,0,0; 0,0,1; 0,1,1], by decide⟩
private theorem cubic_cube : cubic ^ 3 = 1 := by decide
private theorem cubic_apply (x : Vector) : W cubic x = ![x 0,x 2,x 1 + x 2] := by
  change Matrix.mulVec _ x = _
  ext i
  fin_cases i <;> simp [cubic,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]
private theorem cubic_norm (x : Vector) :
    x + W cubic x + W cubic (W cubic x) = x 0 • Pi.single 0 1 := by
  revert x
  decide
private theorem cubic_fixed (x : Space) (hx : action cubic x = x) :
    x ∈ pairedPlane (Pi.single 0 1) (LinearMap.proj 0) := by
  have h1 : W cubic x.1 = x.1 := congrArg Prod.fst hx
  have h2 : W.dual cubic x.2 = x.2 := congrArg Prod.snd hx
  have hn : x.1 = x.1 0 • Pi.single 0 1 := by
    have hh := cubic_norm x.1
    rw [h1,h1] at hh
    simpa only [ZModModule.add_self,zero_add] using hh
  have hd : x.2 = x.2 (Pi.single 0 1) • LinearMap.proj 0 := by
    apply LinearMap.ext
    intro y
    have hf (y : Vector) : x.2 (W cubic y) = x.2 y := by
      have hh := LinearMap.congr_fun h2 (W cubic y)
      change x.2 (W cubic⁻¹ (W cubic y)) = x.2 (W cubic y) at hh
      rw [Representation.inv_self_apply] at hh
      exact hh.symm
    have hh := congrArg x.2 (cubic_norm y)
    rw [map_add,map_add,hf,hf,hf,map_smul] at hh
    simpa only [CharTwo.add_self_eq_zero,zero_add,LinearMap.smul_apply,LinearMap.proj_apply,
      smul_eq_mul,mul_comm] using hh
  rw [pairedPlane,Submodule.mem_span_pair]
  refine ⟨x.1 0,x.2 (Pi.single 0 1),?_⟩
  apply Prod.ext
  · simpa using hn.symm
  · simpa using hd.symm

private theorem cubic_pair : W cubic (Pi.single 0 1) = Pi.single 0 1 ∧
    W.dual cubic (LinearMap.proj 0) = LinearMap.proj 0 := by
  constructor
  · rw [cubic_apply]; ext i; fin_cases i <;> simp
  · apply LinearMap.ext
    intro x
    change (W cubic⁻¹ x) 0 = x 0
    have hi : cubic⁻¹ = cubic*cubic := by decide
    rw [hi,map_mul,Module.End.mul_apply,cubic_apply,cubic_apply]
    rfl

/-- A literal cubic in each paired-plane fixer has exactly that fixed plane. -/
theorem pairedPlane_cubic (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    ∃ g : Group, g ^ 3 = 1 ∧ W g v = v ∧ W.dual g f = f ∧
      ∀ x : Space, action g x = x → x ∈ pairedPlane v f := by
  obtain ⟨a,hav,haf⟩ := paired_transitive (Pi.single 0 1) v (LinearMap.proj 0) f (by simp) hfv
  let g := (MulAut.conj a) cubic
  have hc : g ^ 3 = 1 := by change ((MulAut.conj a) cubic) ^ 3 = 1; rw [← map_pow,cubic_cube,map_one]
  have hact (x : Space) : action g x = action a (action cubic (action a⁻¹ x)) := by
    change action (a*cubic*a⁻¹) x = _
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply]
  refine ⟨g,hc,?_,?_,?_⟩
  · rw [← hav]
    change W (a*cubic*a⁻¹) (W a _) = _
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,Representation.inv_self_apply,
      cubic_pair.1]
  · rw [← haf]
    change W.dual (a*cubic*a⁻¹) (W.dual a _) = _
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,Representation.inv_self_apply,
      cubic_pair.2]
  · intro x hx
    have hh : action cubic (action a⁻¹ x) = action a⁻¹ x := by
      have hh := congrArg (action a⁻¹) hx
      rw [hact,Representation.inv_self_apply] at hh
      exact hh
    obtain ⟨r,s,hrs⟩ := Submodule.mem_span_pair.mp (cubic_fixed _ hh)
    have he := congrArg (action a) hrs
    rw [map_add,map_smul,map_smul,Representation.self_inv_apply] at he
    have hv : action a (Pi.single 0 1,0) = (v,0) := Prod.ext hav (map_zero (W.dual a))
    have hf : action a (0,LinearMap.proj 0) = (0,f) := Prod.ext (map_zero (W a)) haf
    rw [hv,hf] at he
    exact Submodule.mem_span_pair.mpr ⟨r,s,he⟩

private def coordinates {G : Type*} [_root_.Group G] (W₀ : Subgroup G)
    [IsElementaryAbelian 2 W₀] (E : Additive W₀ ≃ₗ[ZMod 2] Space) (x : Space) : G :=
  (E.symm x).toMul

private theorem coordinates_injective {G : Type*} [_root_.Group G] (W₀ : Subgroup G)
    [IsElementaryAbelian 2 W₀] (E : Additive W₀ ≃ₗ[ZMod 2] Space) :
    Function.Injective (coordinates W₀ E) := by
  intro x y h
  apply E.symm.injective
  exact Additive.toMul.injective (Subtype.ext h)

private theorem coordinates_sub {G : Type*} [_root_.Group G] (W₀ : Subgroup G)
    [IsElementaryAbelian 2 W₀] (E : Additive W₀ ≃ₗ[ZMod 2] Space) (x y : Space) :
    coordinates W₀ E (x-y) = coordinates W₀ E x * (coordinates W₀ E y)⁻¹ := by
  change ((E.symm (x-y)).toMul : G) = _
  rw [map_sub]
  change (E.symm x).toMul.val / (E.symm y).toMul.val = _
  exact div_eq_mul_inv _ _

private theorem coordinates_mem_plane {G : Type*} [_root_.Group G] (W₀ : Subgroup G)
    [IsElementaryAbelian 2 W₀] (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (x : Space) :
    coordinates W₀ E x ∈ ambientPlane W₀ E v f ↔ x ∈ pairedPlane v f := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hh : Additive.ofMul w = E.symm x := Additive.toMul.injective (Subtype.ext he)
    change E (Additive.ofMul w) ∈ pairedPlane v f at hw
    rwa [hh,E.apply_symm_apply] at hw
  · intro hx
    exact ⟨(E.symm x).toMul,by change E (E.symm x) ∈ pairedPlane v f; rwa [E.apply_symm_apply],rfl⟩

section Ambient
variable {G : Type*} [_root_.Group G] [Finite G] (W₀ L : Subgroup G)
    [IsElementaryAbelian 2 W₀] (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (CFSG.Quasithin.ChapterE.automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))

omit [Finite G] in
include hE in
private theorem coordinates_conj (l : L) (x : Space) :
    coordinates W₀ E (action (q l) x) = (l : G) * coordinates W₀ E x * (l : G)⁻¹ := by
  have hh := congrArg (fun z : Space => ((E.symm z).toMul : G)) (hE l (E.symm x))
  simp only [E.symm_apply_apply,E.apply_symm_apply] at hh
  exact hh.symm

omit [Finite G] in
include hE in
private theorem component_plane_fixer (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (l : L) :
    (l : G) ∈ centralizer (ambientPlane W₀ E v f : Set G) ↔ q l ∈ pairFixer v f := by
  have hiff (x : Space) : action (q l) x = x ↔
      coordinates W₀ E x * (l : G) = (l : G) * coordinates W₀ E x := by
    rw [← (coordinates_injective W₀ E).eq_iff,coordinates_conj W₀ L hLN q E hE]
    exact ⟨fun hh => (mul_inv_eq_iff_eq_mul.mp hh).symm,
      fun hh => mul_inv_eq_iff_eq_mul.mpr hh.symm⟩
  constructor
  · intro hc
    constructor
    · exact congrArg Prod.fst ((hiff (v,0)).mpr (hc _
        ((coordinates_mem_plane W₀ E v f _).mpr (Submodule.subset_span (by simp)))))
    · exact congrArg Prod.snd ((hiff (0,f)).mpr (hc _
        ((coordinates_mem_plane W₀ E v f _).mpr (Submodule.subset_span (by simp)))))
  · intro hp x hx
    let w : Additive W₀ := Additive.ofMul ⟨x,ambientPlane_le_orbit W₀ E v f hx⟩
    have he : coordinates W₀ E (E w) = x := by simp [coordinates,w]
    have hx' : E w ∈ pairedPlane v f := (coordinates_mem_plane W₀ E v f _).mp (he.symm ▸ hx)
    have hfix : pairedPlane v f ≤ fixedSpace action (zpowers (q l)) := by
      apply (pairedPlane_le_iff v f _).mpr
      exact ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr (Prod.ext hp.1 (map_zero (W.dual (q l)))),
        (mem_fixedSpace_zpowers_iff _ _ _).mpr (Prod.ext (map_zero (W (q l))) hp.2)⟩
    have hh := (hiff (E w)).mp ((mem_fixedSpace_zpowers_iff _ _ _).mp (hfix hx'))
    rwa [he] at hh

include hE hq in
/-- The original two-residual has enough movement to supplement the paired plane. -/
theorem pairedPlane_residual_supplement (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) :
    ambientPlane W₀ E v f ⊔ ⁅W₀,localResidual L (ambientPlane W₀ E v f)⁆ = W₀ := by
  let U := ambientPlane W₀ E v f
  let C := L ⊓ centralizer (U : Set G)
  let R := localResidual L U
  let N := U ⊔ ⁅W₀,R⁆
  let qC : C →* pairFixer v f := (q.comp (inclusion inf_le_left)).codRestrict _
    (fun c => (component_plane_fixer W₀ L hLN q E hE v f ⟨c,c.property.1⟩).mp c.property.2)
  have hqC : Function.Surjective qC := by
    intro g
    obtain ⟨l,hl⟩ := hq g
    refine ⟨⟨l,l.property,?_⟩,Subtype.ext hl⟩
    exact (component_plane_fixer W₀ L hLN q E hE v f l).mpr (hl.symm ▸ g.property)
  obtain ⟨g,hg,hgv,hgf,hfix⟩ := pairedPlane_cubic v f hfv
  let a : pairFixer v f := ⟨g,hgv,hgf⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext hg
  have haR : a ∈ pResidual 2 (pairFixer v f) := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha3))
  rw [← map_pResidual_of_surjective 2 qC hqC] at haR
  obtain ⟨r,hr,he⟩ := haR
  let l : L := ⟨r,r.property.1⟩
  have hl : q l = g := congrArg Subtype.val he
  have hrR : (l : G) ∈ R := mem_map_of_mem C.subtype hr
  have hRN : R ≤ normalizer (W₀ : Set G) := (map_subtype_le _).trans (inf_le_left.trans hLN)
  apply le_antisymm
  · exact sup_le (ambientPlane_le_orbit W₀ E v f)
      (le_normalizer_iff_commutator_le_left.mp hRN)
  · intro z hz
    let x := E (Additive.ofMul (⟨z,hz⟩ : W₀))
    have hx : coordinates W₀ E x = z := by simp [coordinates,x]
    let y := action g x
    let d := action g y - y
    let n := x + y + action g y
    have hd : coordinates W₀ E d ∈ ⁅W₀,R⁆ := by
      change coordinates W₀ E (action g y - y) ∈ _
      rw [← hl,coordinates_sub,coordinates_conj W₀ L hLN q E hE]
      rw [commutator_comm]
      exact commutator_mem_commutator hrR (E.symm y).toMul.property
    have hg3 : action g (action g (action g x)) = x := by
      have hh := congrArg (fun b : Group => action b x) hg
      simpa only [pow_succ,pow_zero,mul_one,map_mul,Module.End.mul_apply,
        map_one,Module.End.one_apply] using hh
    have hn : coordinates W₀ E n ∈ U := by
      apply (coordinates_mem_plane W₀ E v f n).mpr
      apply hfix
      change action g (x + action g x + action g (action g x)) = _
      rw [map_add,map_add,hg3]
      dsimp [n,y]
      abel
    have hnd : n-d = x := by
      dsimp [n,d]
      rw [ZModModule.sub_eq_add,ZModModule.sub_eq_add]
      calc
        x + y + action g y + (action g y + y) =
            x + (y+y) + (action g y + action g y) := by abel
        _ = x := by rw [ZModModule.add_self,ZModModule.add_self]; simp
    rw [← hx,← hnd,coordinates_sub]
    exact N.mul_mem ((show U ≤ N from le_sup_left) hn)
      (N.inv_mem ((show ⁅W₀,R⁆ ≤ N from le_sup_right) hd))
end Ambient


/-- A residual supplement to a centralized plane eliminates the odd core
inside an SQTK overgroup with characteristic-two intersection. -/
theorem oddCore_eq_bot_of_residual_supplement
    {G : Type*} [_root_.Group G] [Finite G] (W₀ U R H M : Subgroup G)
    [IsElementaryAbelian 2 W₀] (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer (W₀ : Set G)) (hWH : W₀ ≤ H) (hRH : R ≤ H)
    (hgen : U ⊔ ⁅W₀,R⁆ = W₀) (hHC : H ≤ centralizer (U : Set G))
    (hWM : centralizer (W₀ : Set G) ≤ M)
    (hSQ : CFSG.Quasithin.IsStronglyQuasithin H)
    (hMH : CFSG.Quasithin.HasCharacteristicTwo (H ⊓ M : Subgroup G)) :
    pPrimeCore 2 H = ⊥ := by
  let A := ⁅W₀,R⁆
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp hRN
  have hAH : A ≤ H := hAW.trans hWH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hpR : IsPPerfect 2 (R.subgroupOf H) := hR.of_surjective
    (subgroupOfEquivOfLe hRH).symm.toMonoidHom (subgroupOfEquivOfLe hRH).symm.surjective
  have hcomm : ⁅A.subgroupOf H,R.subgroupOf H⁆ = A.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hRH]
    exact commutator_isPPerfect_idempotent R W₀ hR (IsElementaryAbelian.isPGroup 2 W₀) hRN
  have hcent := CFSG.Quasithin.ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hSQ
    (R.subgroupOf H) (A.subgroupOf H) hpR hcomm
  let O := (pPrimeCore 2 H).map H.subtype
  have hAO : ⁅A,O⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map H.subtype) hcent
    simpa only [map_commutator,map_subgroupOf_eq_of_le hAH,Subgroup.map_bot] using hh
  have hOW : O ≤ centralizer (W₀ : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hgen]
    exact sup_le (le_centralizer_iff.mp ((map_subtype_le _).trans hHC))
      (commutator_eq_bot_iff_le_centralizer.mp hAO)
  have hOM : O ≤ M := hOW.trans hWM
  let N := M.subgroupOf H
  have hcN : CFSG.Quasithin.HasCharacteristicTwo N := by
    have hh := hMH.of_equiv (subgroupOfEquivOfLe (H := H ⊓ M) inf_le_left).symm
    exact hh.of_equiv (MulEquiv.subgroupCongr (inf_subgroupOf_left M H))
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 H).subgroupOf N)) := by
    rw [← inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe (H := pPrimeCore 2 H ⊓ N) inf_le_right).toEquiv]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le inf_le_left)
  have hz : (pPrimeCore 2 H).subgroupOf N = ⊥ := by
    have hh : (pPrimeCore 2 H).subgroupOf N ≤ pPrimeCore 2 N := le_sSup ⟨inferInstance,hcop⟩
    rw [Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hcN] at hh
    exact le_bot_iff.mp hh
  apply le_bot_iff.mp
  intro x hx
  have hm : x ∈ N := hOM (mem_map_of_mem H.subtype hx)
  have hh : (⟨x,hm⟩ : N) ∈ (pPrimeCore 2 H).subgroupOf N := hx
  rw [hz] at hh
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddCore
