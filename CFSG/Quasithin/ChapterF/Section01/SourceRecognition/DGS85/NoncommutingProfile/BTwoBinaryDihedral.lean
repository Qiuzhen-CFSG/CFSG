module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryCenterAction
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.SpecificGroups.DihedralEightFixedInvolution

/-!
# The actual binary residual dihedral subgroup and its normalizer

In the strict binary branch, the residual R_alpha has order two and its
nonidentity element inverts the cyclic center of V_beta = Q₈ ◦ C₄.
Consequently the literal subgroup Δ = R_alpha Z(V_beta) is dihedral of
order eight inside the original beta core. This Δ is the auxiliary D
on printed p.162, distinct from the original elementary D_alpha.

An automorphism of Δ fixing its residual involution is either trivial
or conjugation by that involution. The beta enlargement normalizes V_beta,
so its residual normalizer factors as R_alpha C_Lbeta(Δ), with trivial
intersection. Multiplication by the correcting residual element retains
the beta-core coset, as required for the source's choice of t'. The
original F1.11 application constructs the radius marking and inversion
internally, keeping one opposite-center lift and the literal core maps.

This proves the dihedral recognition and normalizer correction used in
the binary proof of (10.8). Constructing the endpoint-exchanging actor in
this normalizer and the terminal-core contradiction remain separate steps.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed pp.161--162. The dihedral presentation and fixed-involution
automorphism calculation are reused from the group-theory library.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

private theorem quaternion_center_generator
    {G : Type*} [Group G] (V : Subgroup G) (e : V ≃* QuaternionCyclic.Model) :
    ∃ z : G, orderOf z=4 ∧ centerIn V=zpowers z := by
  let zV := e.symm QuaternionCyclic.r
  let z : G := zV
  have hzorder : orderOf z=4 := by
    rw [show orderOf z=orderOf zV from Subgroup.orderOf_coe zV]
    exact (e.symm.orderOf_eq _).trans QuaternionCyclic.r_order
  have hz : z∈centerIn V := by
    refine ⟨zV.property,?_⟩
    intro v hv
    apply congrArg (Subtype.val : V → G) (a₁ := (⟨v,hv⟩:V)*zV) (a₂ := zV*⟨v,hv⟩)
    apply e.injective
    have hr : QuaternionCyclic.r∈center QuaternionCyclic.Model := by
      rw [QuaternionCyclic.center_eq_cyclic]
      exact ⟨Multiplicative.ofAdd 1,rfl⟩
    simpa only [map_mul,zV,e.apply_symm_apply] using mem_center_iff.mp hr (e ⟨v,hv⟩)
  refine ⟨z,hzorder,le_antisymm ?_ (zpowers_le.mpr hz)⟩
  intro x hx
  have hx' : e ⟨x,hx.1⟩∈center QuaternionCyclic.Model := by
    apply mem_center_iff.mpr
    intro v
    obtain ⟨v,rfl⟩ := e.surjective v
    have hh : v*(⟨x,hx.1⟩:V)=⟨x,hx.1⟩*v := Subtype.ext (hx.2 v v.property)
    simpa only [map_mul] using congrArg e hh
  have model : ∀ x : QuaternionCyclic.Model, (∀ y,y*x=x*y) →
      ∃ i : Fin 4, x=QuaternionCyclic.r^i.val := by decide +kernel
  obtain ⟨i,hi⟩ := model _ (mem_center_iff.mp hx')
  have hval : x=z^i.val := by
    apply congrArg (Subtype.val : V → G) (a₁ := (⟨x,hx.1⟩:V)) (a₂ := zV^i.val)
    apply e.injective
    simpa only [map_pow,zV,e.apply_symm_apply] using hi
  exact hval ▸ (zpowers z).pow_mem (mem_zpowers z) _

private theorem dihedral_of_residual_inversion
    {G : Type*} [Group G] (V R : Subgroup G) [Finite R]
    (e : V≃*QuaternionCyclic.Model) (hRcard : Nat.card R=2)
    (hinv : ∀ r∈R,r≠1 → ∀ z∈centerIn V,r*z*r⁻¹=z⁻¹) :
    ∃ r∈R, r≠1 ∧ r^2=1 ∧ R=zpowers r ∧
      r∉centerIn (R⊔centerIn V) ∧ Nat.card (R⊔centerIn V : Subgroup G)=8 ∧
      Nonempty ((R⊔centerIn V : Subgroup G)≃*DihedralGroup 4) := by
  have hRne : R≠⊥ := by intro hh; rw [hh,card_bot] at hRcard; contradiction
  obtain ⟨r,hr,hr1⟩ := R.bot_or_exists_ne_one.resolve_left hRne
  have hr2 : r^2=1 := by
    have hh := pow_card_eq_one' (x:=(⟨r,hr⟩:R))
    rw [hRcard] at hh
    exact congrArg Subtype.val hh
  have hReq : R=zpowers r := (eq_of_le_of_card_ge (zpowers_le.mpr hr) (by
    rw [Nat.card_zpowers,orderOf_eq_prime hr2 hr1,hRcard])).symm
  obtain ⟨z,hzorder,hZ⟩ := quaternion_center_generator V e
  have hz : z∈centerIn V := hZ ▸ mem_zpowers z
  have hconj := hinv r hr hr1 z hz
  have hz2 : z^2≠1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hzorder] at hd
    norm_num at hd
  have hrout : r∉centerIn V := by
    intro hh
    have he : z=z⁻¹ := by rw [←hh.2 z hz.1,mul_inv_cancel_right] at hconj; exact hconj
    exact hz2 ((pow_two z).trans ((congrArg (z*·) he).trans (mul_inv_cancel z)))
  have hrn : r∈normalizer (zpowers z : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (r*z*r⁻¹)=zpowers z
    rw [hconj,zpowers_inv]
  let T := R⊔centerIn V
  have hcard : Nat.card T=8 := by
    change Nat.card (R⊔centerIn V : Subgroup G)=8
    rw [hReq,hZ,sup_comm,card_sup_zpowers_of_normalizing_involution _ r hr2
      (hZ ▸ hrout) hrn,Nat.card_zpowers,hzorder]
  have hrT : r∈T := mem_sup_left hr
  have hzT : z∈T := mem_sup_right hz
  have hrnon : r∉centerIn T := by
    intro hh
    have he : z=z⁻¹ := by rw [←hh.2 z hzT,mul_inv_cancel_right] at hconj; exact hconj
    exact hz2 ((pow_two z).trans ((congrArg (z*·) he).trans (mul_inv_cancel z)))
  let zT : T := ⟨z,hzT⟩
  let rT : T := ⟨r,hrT⟩
  have hgen : closure ({zT,rT}:Set T)=⊤ := by
    apply map_injective T.subtype_injective
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      ←MonoidHom.range_eq_map,T.range_subtype]
    change closure ({z,r}:Set G)=R⊔centerIn V
    rw [←Set.singleton_union,Subgroup.closure_union,←zpowers_eq_closure,←zpowers_eq_closure,hReq,hZ,sup_comm]
  have heq := dihedralGroup_equiv_of_presentation (by decide : 0<4) zT rT
    ((Subgroup.orderOf_coe zT).symm.trans hzorder)
    (Subtype.ext hr2) (Subtype.ext hconj) hgen hcard
  exact ⟨r,hr,hr1,hr2,hReq,hrnon,hcard,heq⟩

private theorem dihedral_normalizer_correction
    {G : Type*} [Group G] (V R : Subgroup G) (r : G)
    (hr : r∈R) (hr1 : r≠1) (hr2 : r^2=1) (hReq : R=zpowers r)
    (hrnon : r∉centerIn (R⊔centerIn V))
    (e : (R⊔centerIn V : Subgroup G)≃*DihedralGroup 4)
    (x : G) (hxR : x∈normalizer (R:Set G))
    (hxV : x∈normalizer (V:Set G)) :
    ∃ a∈R, x*a∈centralizer ((R⊔centerIn V : Subgroup G):Set G) := by
  classical
  let T := R⊔centerIn V
  have hxZ : x∈normalizer (centerIn V:Set G) :=
    normalizes_centerIn (S:=V) (A:=normalizer (V:Set G)) le_rfl hxV
  have hxT : x∈normalizer (T:Set G) := (normalizer_inf_normalizer_le_normalizer_sup R (centerIn V)) ⟨hxR,hxZ⟩
  let rT : T := ⟨r,mem_sup_left hr⟩
  let f : MulAut T := T.normalizerMonoidHom ⟨x,hxT⟩
  have hfix : f rT=rT := by
    have hxr : x*r*x⁻¹∈R := (mem_normalizer_iff.mp hxR r).mp hr
    rw [hReq] at hxr
    have hfinite : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hr2⟩
    rw [hfinite.mem_zpowers_iff_mem_range_orderOf,orderOf_eq_prime hr2 hr1] at hxr
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hxr
    have hi2 := Finset.mem_range.mp hi
    have hxr1 : x*r*x⁻¹≠1 := by
      intro hh
      apply hr1
      exact (MulAut.conj x).injective (hh.trans (map_one (MulAut.conj x)).symm)
    have heq : x*r*x⁻¹=r := by
      interval_cases i
      · simp only [pow_zero] at he
        exact (hxr1 he.symm).elim
      · simpa only [pow_one] using he.symm
    exact Subtype.ext heq
  have hrnon' : rT∉center T := by
    intro hh
    apply hrnon
    refine ⟨rT.property,?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hh ⟨y,hy⟩)
  rcases DihedralGroup.aut_eq_one_or_conj_of_fixed_involution_of_equiv
      e rT (Subtype.ext hr2) hrnon' f hfix with hh|hh
  · refine ⟨1,one_mem R,?_⟩
    rw [mul_one]
    intro y hy
    have he := congrArg Subtype.val (DFunLike.congr_fun hh (⟨y,hy⟩:T))
    change x*y*x⁻¹=y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · refine ⟨r,hr,?_⟩
    intro y hy
    have he := congrArg Subtype.val (DFunLike.congr_fun hh (⟨y,hy⟩:T))
    change x*y*x⁻¹=r*y*r⁻¹ at he
    have hcomm : x*r=r*x := by
      have hh := congrArg Subtype.val hfix
      change x*r*x⁻¹=r at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hri : r⁻¹=r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr2)
    have he' := congrArg (fun z:G => r*z*x) he
    have hrr : r*r=1 := by simpa only [pow_two] using hr2
    have hresult : y*(r*x)=(r*x)*y := by
      simpa only [hri,mul_assoc,inv_mul_cancel,mul_one,←mul_assoc r r,hrr,one_mul] using he'.symm
    simpa only [hcomm] using hresult


private theorem dihedral_normalizer_product
    {G : Type*} [Group G] (H V R : Subgroup G) [Finite R]
    (hRH : R≤H) (hHV : H≤normalizer (V:Set G))
    (hRcard : Nat.card R=2) (e : V≃*QuaternionCyclic.Model)
    (hinv : ∀ r∈R,r≠1 → ∀ z∈centerIn V,r*z*r⁻¹=z⁻¹) :
    Nat.card (R⊔centerIn V : Subgroup G)=8 ∧
      Nonempty ((R⊔centerIn V : Subgroup G)≃*DihedralGroup 4) ∧
      H⊓normalizer (R:Set G)=R⊔(H⊓centralizer ((R⊔centerIn V : Subgroup G):Set G)) ∧
      Disjoint R (centralizer ((R⊔centerIn V : Subgroup G):Set G)) ∧
      ∀ x∈H, x∈normalizer (R:Set G) →
        ∃ a∈R, x*a∈H⊓centralizer ((R⊔centerIn V : Subgroup G):Set G) := by
  obtain ⟨r,hr,hr1,hr2,hReq,hrnon,hcard,⟨eT⟩⟩ :=
    dihedral_of_residual_inversion V R e hRcard hinv
  let T := R⊔centerIn V
  have hcorrect (x : G) (hx : x∈H) (hxR : x∈normalizer (R:Set G)) :
      ∃ a∈R, x*a∈H⊓centralizer (T:Set G) := by
    obtain ⟨a,ha,hc⟩ := dihedral_normalizer_correction V R r hr hr1 hr2 hReq hrnon eT x hxR (hHV hx)
    exact ⟨a,ha,H.mul_mem hx (hRH ha),hc⟩
  refine ⟨hcard,⟨eT⟩,?_,?_,hcorrect⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨a,ha,hxa⟩ := hcorrect x hx.1 hx.2
      have hh := (R⊔(H⊓centralizer (T:Set G))).mul_mem
        (mem_sup_right hxa) (mem_sup_left (R.inv_mem ha))
      simpa only [mul_inv_cancel_right] using hh
    · refine sup_le (le_inf hRH R.le_normalizer) (le_inf inf_le_left ?_)
      exact (inf_le_right.trans (centralizer_le (show R≤T from le_sup_left))).trans
        (centralizer_le_normalizer R)
  · apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    by_contra hx1
    have hxn : x≠1 := by simpa only [mem_bot] using hx1
    have hRcyc : IsCyclic R := isCyclic_of_prime_card hRcard
    let := hRcyc
    have hxorder : orderOf (⟨x,hx.1⟩:R)=2 := orderOf_eq_prime
      (by
        have hh := pow_card_eq_one' (x:=(⟨x,hx.1⟩:R))
        rwa [hRcard] at hh) (fun hh => hxn (congrArg Subtype.val hh))
    have hrorder : orderOf (⟨r,hr⟩:R)=2 := orderOf_eq_prime (Subtype.ext hr2)
      (fun hh => hr1 (congrArg Subtype.val hh))
    have hxr : x=r := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hxorder hrorder)
    exact hrnon ⟨mem_sup_left hr,hxr ▸ hx.2⟩

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The dihedral subgroup used in the binary separation argument is formed
from the actual residual and the actual radius center. Its normalizer in the
original beta enlargement splits over its centralizer, and the correcting
residual element preserves the beta-core coset. -/
theorem original_bTwo_binary_dihedral_normalizer
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    ∃ g∈graphLocalGroup F α, g • β=t ∧
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let V₁ := (V F β 1).map ι
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      let Δ := R₀⊔centerIn V₁
      let L₁ := enlargedEndpoint L S 1
      Nat.card R₀=2 ∧ Δ≤Q₁ ∧ Nat.card Δ=8 ∧ Nonempty (Δ≃*DihedralGroup 4) ∧
      L₁⊓normalizer (R₀:Set G)=R₀⊔(L₁⊓centralizer (Δ:Set G)) ∧
      Disjoint R₀ (centralizer (Δ:Set G)) ∧
      ∀ x∈L₁, x∈normalizer (R₀:Set G) →
        ∃ a∈R₀, x*a∈L₁⊓centralizer (Δ:Set G) ∧ (x*a∈Q₁ ↔ x∈Q₁) := by
  obtain ⟨g,hg,hgt,hRcard,⟨eV⟩,hfaith,hker,hcent,hinv⟩ :=
    original_bTwo_binary_residual_center_action h hc hne hb hβu ht htne e hK hD
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let V₁ := (V F β 1).map ι
  let R := (Q₁⊓(Q F t).map ι)⊓centralizer
    (((Z F u).map ι⊔(Z F (g • u)).map ι : Subgroup G):Set G)
  let L₁ := enlargedEndpoint L S 1
  have hRle : R≤Q₁ := inf_le_left.trans inf_le_left
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite R := Finite.of_injective (inclusion hRle) (inclusion_injective _)
  have hVQ : V₁≤Q₁ := by
    have hh := map_mono (f:=ι) (graph_V_le_Q_of_short (reduced_triple h)
      (reduced_kernel_sylow h) β (i:=1) (by change 1<b F; rw [hb]; decide))
    change V₁≤(Q F β).map ι at hh
    rwa [reduced_base_Q_map h true] at hh
  have hQL : Q₁≤L₁ := by
    have hcore : Q F β≤graphLocalGroup F β := by
      let := finite_endpoints (reduced_triple h)
      obtain ⟨T⟩ := Sylow.nonempty (p:=2) (G:=stabilizer F β)
      exact (pCoreIn_le_sylow _ T).trans (sylow_le_sylowGenerated _ T)
    have hh := map_mono (f:=ι) hcore
    rwa [reduced_base_Q_map h true,reduced_graphLocalGroup_image h true] at hh
  have hLV : L₁≤normalizer (V₁:Set G) := by
    have hn : graphLocalGroup F β≤normalizer (V F β 1:Set (G₀ L S)) :=
      (sylowGenerated_le _).trans (graph_stabilizer_normalizes_V (reduced_triple h) β 1)
    have hh := (map_mono (f:=ι) hn).trans ((V F β 1).le_normalizer_map ι)
    rwa [reduced_graphLocalGroup_image h true] at hh
  obtain ⟨hcard,heq,hfactor,hdis,hcor⟩ := dihedral_normalizer_product L₁ V₁ R
    (hRle.trans hQL) hLV hRcard eV hinv
  refine ⟨g,hg,hgt,hRcard,sup_le hRle (inf_le_left.trans hVQ),hcard,heq,hfactor,hdis,?_⟩
  intro x hx hxn
  obtain ⟨a,ha,hxa⟩ := hcor x hx hxn
  refine ⟨a,ha,hxa,?_⟩
  constructor
  · intro hxaQ
    simpa only [mul_inv_cancel_right] using Q₁.mul_mem hxaQ (Q₁.inv_mem (hRle ha))
  · intro hxQ
    exact Q₁.mul_mem hxQ (hRle ha)

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
