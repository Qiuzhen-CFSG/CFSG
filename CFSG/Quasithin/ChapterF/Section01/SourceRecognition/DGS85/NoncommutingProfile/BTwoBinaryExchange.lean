module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryDihedral

/-!
# Binary D-conjugacy and the actual exchanging actor

The faithful residual pairing supplies a nontrivial commutator with each
of the two neighboring core intersections. Each commutator takes values
in a central subgroup of order two. These two central subgroups generate
Z_alpha, so Q_alpha is transitive by conjugation on D_alpha minus Z_alpha.
All subgroups are the literal original images, with the same quotient
marking and both endpoint cores retained.

If the tested terminal intersection R_alpha ∩ Q_y is nontrivial, its
order-two residual is contained in Q_y. Local transitivity first gives
an element taking alpha to alpha'. The D-conjugacy theorem corrects it
inside Q_alpha to normalize R_alpha. The dihedral normalizer correction
then produces an actual element centralizing Delta = R_alpha Z(V_beta),
still taking alpha to alpha' and still outside the original beta core.

The terminal intersection remains a contradiction hypothesis: this module
does not assert its vanishing. The remaining source step is to place the
corrected actor in the third neighboring core and apply that core's
centralizer structure. The full strict path and Chapter 10 assembly also
remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed pp.161--162, especially the conjugacy and choice of t'
on p.162. Earlier source actions and field bounds are constructed from
original HypothesisF11 in both public applications.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

private theorem centralizer_of_residual_product
    {G : Type*} [Group G] (D Z R I : Subgroup G)
    (hD : D=Z⊔R) (hZR : Z≤centralizer (R:Set G))
    (hZI : Z≤centralizer (I:Set G)) (hf : R⊓centralizer (I:Set G)=⊥) :
    D⊓centralizer (I:Set G)=Z := by
  apply le_antisymm
  · intro x hx
    have hp : x∈(Z:Set G)*(R:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (hZR.trans (Subgroup.centralizer_le_normalizer _)),←hD]
      exact hx.1
    obtain ⟨z,hz,r,hr,rfl⟩ := hp
    have hrc : r∈centralizer (I:Set G) := by
      simpa only [inv_mul_cancel_left] using
        (centralizer (I:Set G)).mul_mem ((centralizer _).inv_mem (hZI hz)) hx.2
    have hr1 : r=1 := mem_bot.mp (hf ▸ ⟨hr,hrc⟩)
    change z*r∈Z
    rw [hr1,mul_one]
    exact hz
  · exact le_inf (hD ▸ le_sup_left) hZI

private theorem two_center_displacement
    {G : Type*} [Group G] (D Z I C : Subgroup G)
    (hc : Nat.card C=2) (hcomm : ⁅I,D⁆≤C)
    (hfix : D⊓centralizer (I:Set G)=Z)
    (x : G) (hx : x∈D) (hxZ : x∉Z) :
    ∀ c∈C, ∃ i∈I, i*x*i⁻¹=c*x := by
  have hn : x∉centralizer (I:Set G) := fun hh => hxZ (hfix ▸ ⟨hx,hh⟩)
  have hex : ∃ i∈I, i*x≠x*i := by
    by_contra! hh
    exact hn hh
  obtain ⟨i,hi,hin⟩ := hex
  have ha : ⁅i,x⁆∈C := hcomm (commutator_mem_commutator hi hx)
  have ha1 : ⁅i,x⁆≠1 := fun hh => hin (commutatorElement_eq_one_iff_commute.mp hh).eq
  obtain ⟨a,ha0,huniq⟩ := (Nat.card_eq_two_iff' (1:C)).mp hc
  have heq (c:G) (hcC : c∈C) (hc1 : c≠1) : c=⁅i,x⁆ := by
    apply congrArg Subtype.val (a₁ := (⟨c,hcC⟩:C)) (a₂ := ⟨⁅i,x⁆,ha⟩)
    exact (huniq _ (fun hh => hc1 (congrArg Subtype.val hh))).trans
      (huniq _ (fun hh => ha1 (congrArg Subtype.val hh))).symm
  intro c hcC
  by_cases hc1 : c=1
  · exact ⟨1,one_mem I,by simp [hc1]⟩
  · refine ⟨i,hi,?_⟩
    rw [heq c hcC hc1]
    simp only [commutatorElement_def]
    group

private theorem binary_residual_coset_conjugacy
    {G : Type*} [Group G] (Q D Z R I C : Subgroup G) (g:G)
    (hDQ : D≤Q) (hIQ : I≤Q) (hD : D=Z⊔R)
    (hRcard : Nat.card R=2) (hZQ : Z≤centralizer (Q:Set G))
    (hfaith : R⊓centralizer (I:Set G)=⊥)
    (hCcard : Nat.card C=2) (hcomm : ⁅I,D⁆≤C)
    (hnQ : g∈normalizer (Q:Set G)) (hnD : g∈normalizer (D:Set G))
    (hnZ : g∈normalizer (Z:Set G)) (hZgen : Z=C⊔C.conjBy g) :
    ∀ x∈D, x∉Z → ∀ y∈D, y∉Z → ∃ q∈Q, q*x*q⁻¹=y := by
  have hZD : Z≤D := hD ▸ le_sup_left
  have hRD : R≤D := hD ▸ le_sup_right
  have hZR : Z≤centralizer (R:Set G) := hZQ.trans (centralizer_le (hRD.trans hDQ))
  have hZI : Z≤centralizer (I:Set G) := hZQ.trans (centralizer_le hIQ)
  have hfix := centralizer_of_residual_product D Z R I hD hZR hZI hfaith
  have hreach (x:G) (hx:x∈D) (hxn:x∉Z) (z:G) (hz:z∈Z) :
      ∃ q∈Q, q*x*q⁻¹=z*x := by
    have hCZ : C≤Z := hZgen ▸ le_sup_left
    have hCgZ : C.conjBy g≤Z := hZgen ▸ le_sup_right
    have hn : C≤normalizer (C.conjBy g:Set G) :=
      (hCZ.trans hZQ).trans ((centralizer_le (hCgZ.trans (hZD.trans hDQ))).trans
        (Subgroup.centralizer_le_normalizer _))
    have hp : z∈(C:Set G)*(C.conjBy g:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ hn,←hZgen]
      exact hz
    obtain ⟨a,ha,b,hb,rfl⟩ := hp
    have hb0 := hb
    obtain ⟨c,hc,hcb⟩ := hb
    change g*c*g⁻¹=b at hcb
    obtain ⟨i,hi,hia⟩ := two_center_displacement D Z I C hCcard hcomm hfix x hx hxn a ha
    let x' := g⁻¹*x*g
    have hx' : x'∈D := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer (D:Set G)).inv_mem hnD) x).mp hx
    have hxn' : x'∉Z := by
      intro hh
      have hh' := (mem_normalizer_iff.mp hnZ x').mp hh
      apply hxn
      simpa only [x',mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh'
    obtain ⟨j,hj,hjc⟩ := two_center_displacement D Z I C hCcard hcomm hfix x' hx' hxn' c hc
    let k := g*j*g⁻¹
    have hk : k∈Q := (mem_normalizer_iff.mp hnQ j).mp (hIQ hj)
    have hkb : k*x*k⁻¹=b*x := by
      have hh := congrArg (MulAut.conj g) hjc
      dsimp only [MulAut.conj_apply,x'] at hh
      rw [←hcb]
      dsimp only [k]
      calc
        _=g*(j*(g⁻¹*x*g)*j⁻¹)*g⁻¹ := by group
        _=g*(c*(g⁻¹*x*g))*g⁻¹ := hh
        _=(g*c*g⁻¹)*x := by group
    refine ⟨i*k,Q.mul_mem (hIQ hi) hk,?_⟩
    have hbi : i*b=b*i := hZQ (hCgZ hb0) i (hIQ hi)
    calc
      (i*k)*x*(i*k)⁻¹=i*(k*x*k⁻¹)*i⁻¹ := by group
      _=i*(b*x)*i⁻¹ := by rw [hkb]
      _=b*(i*x*i⁻¹) := by rw [←mul_assoc i b,hbi]; group
      _=b*(a*x) := by rw [hia]
      _=(a*b)*x := by rw [←mul_assoc,hZQ (hCZ ha) b (hDQ (hZD (hCgZ hb0))) ]
  intro x hx hxn y hy hyn
  have hfactor (x:G) (hx:x∈D) (hxn:x∉Z) : ∃ z∈Z, ∃ r∈R, r≠1 ∧ x=z*r := by
    have hp : x∈(Z:Set G)*(R:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (hZR.trans (Subgroup.centralizer_le_normalizer _)),←hD]
      exact hx
    obtain ⟨z,hz,r,hr,he⟩ := hp
    change z*r=x at he
    refine ⟨z,hz,r,hr,?_,he.symm⟩
    intro hr1
    apply hxn
    exact (show x=z from by simpa only [hr1,mul_one] using he.symm) ▸ hz
  obtain ⟨z,hz,r,hr,hr1,hx⟩ := hfactor x hx hxn
  obtain ⟨w,hw,s,hs,hs1,hy⟩ := hfactor y hy hyn
  obtain ⟨a,ha,huniq⟩ := (Nat.card_eq_two_iff' (1:R)).mp hRcard
  have hrs : r=s := congrArg Subtype.val
    ((huniq (⟨r,hr⟩:R) (fun hh => hr1 (congrArg Subtype.val hh))).trans
      (huniq (⟨s,hs⟩:R) (fun hh => hs1 (congrArg Subtype.val hh))).symm)
  obtain ⟨q,hq,hqeq⟩ := hreach x (hx ▸ (hD ▸ (Z⊔R).mul_mem (mem_sup_left hz) (mem_sup_right hr))) hxn
    (w*z⁻¹) (Z.mul_mem hw (Z.inv_mem hz))
  refine ⟨q,hq,?_⟩
  rw [hqeq,hx,hy,hrs]
  group

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

/-- In the strict binary branch the actual alpha core is transitive by
conjugation on D_alpha outside its natural center. This is the conjugacy
step used to correct the endpoint-exchanging element in DGS (10.8). -/
theorem original_bTwo_binary_D_conjugacy
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
    let Z₀ := (Z F α).map ι
    ∀ x∈D₀, x∉Z₀ → ∀ y∈D₀, y∉Z₀ → ∃ q∈Q₀, q*x*q⁻¹=y := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,hkmin,n,hn,hm,hpow,g,hg,
    hgen,hfour,hwhole,hRne,hDel,hRel,hdec,hdis,hprod,hZ,hDcard,hQcard,hnP,hnB⟩ :=
    original_bTwo_strict_residual h hc hne hb hβu ht htne hD
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  change c.actor=graphLocalGroup F α at hactor
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hk : Nat.card k=2 := by
    have hh := (c.linear_central_core_structure H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ).1
    rw [hK] at hh
    omega
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁⊓(Q F t).map ι
  let Z₀ := (Z F α).map ι
  let Z₁ := (Z F β).map ι
  let I := Q₀⊓Q₁
  let W₀ := (Z F u).map ι⊔(Z F ((g:G₀ L S) • u)).map ι
  let R := D₀⊓centralizer (W₀:Set G)
  have hQam : (Q F α).map ι=Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F β).map ι=Q₁ := reduced_base_Q_map h true
  have hDm : (D F β t).map ι=D₀ := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hQbm]
  have hRle : Nat.card R≤2 := original_bTwo_binary_residual_card_le_two
    h hc hne hb hβu ht htne c hactor e hK g hg hgen hDel
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite R := Finite.of_injective
    (inclusion (show R≤Q₁ from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  have hRcard : Nat.card R=2 := by
    have hh := R.one_lt_card_iff_ne_bot.mpr hRne
    omega
  have hfaith := Assembly.BTwoSource.original_bTwo_residual_endpoint_centralizer
    h hc hne hb hβu ht htne c hactor eβ g hg hgen hDel
  change R⊓centralizer (I:Set G)=⊥ at hfaith
  have hder : ⁅Q₁,Q₁⁆=Z₁ := by
    have hh := congrArg (map ι) (c.beta_core_frattini_eq H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm).2
    change (⁅Q F β,Q F β⁆).map ι=Z₁ at hh
    rwa [map_commutator,hQbm] at hh
  have hZcard : Nat.card Z₁=2 := by
    rw [show Z₁=(Z F β).map ι from rfl,card_map_of_injective (G₀ L S).subtype_injective]
    exact (c.central_middle_center_card H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _)).trans hk
  have hZQ : Z₀≤centralizer (Q₀:Set G) := by
    have hh := (map_mono (f:=ι) (le_centralizer_iff.mp (graph_Q_centralizes_Z H α))).trans
      (map_centralizer_le_centralizer_image _ _)
    change Z₀≤centralizer ((Q F α).map ι:Set G) at hh
    rwa [hQam] at hh
  obtain ⟨a,ha,hop⟩ := c.exists_opposite_lift H ht htne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry H (reduced_kernel_sylow h) hb a ha hop
  have hDQ : D₀≤Q₀ := by
    have hh := map_mono (f:=ι) d.separated
    change (D F β t).map ι≤(Q F α).map ι at hh
    rwa [hDm,hQam] at hh
  have hgv : (g:G₀ L S) • α=α := c.actor_le g.property
  have image_conj (A : Subgroup (G₀ L S)) :
      (A.map ι).map (MulAut.conj (ι g)).toMonoidHom=
        (A.map (MulAut.conj (g:G₀ L S)).toMonoidHom).map ι := by
    rw [map_map,map_map]
    congr 1
  have hnQ : ι g∈normalizer (Q₀:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Q₀.map (MulAut.conj (ι g)).toMonoidHom=Q₀
    rw [←hQam,image_conj,←Q_translate,hgv]
  have hnZ : ι g∈normalizer (Z₀:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Z₀.map (MulAut.conj (ι g)).toMonoidHom=Z₀
    rw [show Z₀=(Z F α).map ι from rfl,image_conj,←Z_translate,hgv]
  have hnD : ι g∈normalizer (D₀:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change D₀.map (MulAut.conj (ι g)).toMonoidHom=D₀
    have hn := (hd ▸ d.normalized H (reduced_kernel_sylow h) hb) g.property
    change (g:G₀ L S)∈normalizer (D F β t:Set (G₀ L S)) at hn
    rw [←hDm,image_conj]
    exact congrArg (map ι) (mem_normalizer_iff_map_conj_eq.mp hn)
  have hZgen : Z₀=Z₁⊔Z₁.conjBy (ι g) := by
    have hh := congrArg (map ι) (c.central_neighbor_centers H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne).1
    rw [Subgroup.map_sup] at hh
    change Z₀=Z₁⊔(Z F t).map ι at hh
    rw [conjBy,show Z₁=(Z F β).map ι from rfl,image_conj,←Z_translate,hg]
    exact hh
  exact binary_residual_coset_conjugacy Q₀ D₀ Z₀ R I Z₁ (ι g)
    hDQ inf_le_left hdec hRcard hZQ hfaith hZcard
    (hder ▸ commutator_mono inf_le_right inf_le_left) hnQ hnD hnZ hZgen

/-- Under a nontrivial tested terminal intersection, the strict binary residual
admits an actual endpoint-exchanging actor centralizing its dihedral extension.
The actor remains outside the literal beta core. The nontrivial intersection is the
contradiction case of (10.8), not a separation or recognition assumption. -/
theorem original_bTwo_binary_exchanging_actor
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
      Nat.card R₀=2 ∧ Nat.card Δ=8 ∧ Nonempty (Δ≃*DihedralGroup 4) ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠β → R₀⊓(Q F y).map ι≠⊥ →
        ∃ x∈graphLocalGroup F β, x • α=u ∧
          ι x∈enlargedEndpoint L S 1⊓centralizer (Δ:Set G) ∧ ι x∉Q₁ := by
  obtain ⟨g,hg,hgt,hRcard,hΔQ,hΔcard,hΔiso,hfactor,hdis,hcorrect⟩ :=
    original_bTwo_binary_dihedral_normalizer h hc hne hb hβu ht htne e hK hD
  obtain ⟨k,f,fin,ch,alg,c,hactor,hkmin,n,hn,hm,hpow,g',hg',
    hgen,hfour,hwhole,hRne,hDel,hRel,hdec,hdis',hprod,hZ,hDcard,hQcard,hnP,hnB⟩ :=
    original_bTwo_strict_residual h hc hne hb hβu ht htne hD
  change BTwoCenterActionData F α β u k (Fin 2 → k) at c
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β := c.middle
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let V₁ := (V F β 1).map ι
  let D₀ := Q₁⊓(Q F t).map ι
  let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
  let R := D₀⊓centralizer (W₀:Set G)
  let Δ := R⊔centerIn V₁
  change Nat.card R=2 at hRcard
  have hDm : (D F β t).map ι=D₀ := by
    change (Q F β⊓Q F t).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  obtain ⟨a,ha,hop⟩ := c.exists_opposite_lift H ht htne
  obtain ⟨d,hd,_⟩ := c.exists_oppositeGeometry H (reduced_kernel_sylow h) hb a ha hop
  have hDQ : D₀≤Q₀ := by
    have hh := map_mono (f:=ι) d.separated
    change (D F β t).map ι≤(Q F α).map ι at hh
    rwa [hDm,reduced_base_Q_map h false] at hh
  have hRQ : R≤Q₀ := inf_le_left.trans hDQ
  have hRβ : R≤Q₁ := inf_le_left.trans inf_le_left
  have hZaD : (Z F α).map ι≤D₀ := by
    change (Z F α).map ι≤(parabolic L S 1).pCoreIn 2⊓(Q F t).map ι
    rw [hdec]
    exact le_sup_left
  let _ := hDel
  have hZaR : (Z F α).map ι≤centralizer (R:Set G) :=
    (hZaD.trans (le_centralizer D₀)).trans (centralizer_le inf_le_left)
  have hZuR : (Z F u).map ι≤centralizer (R:Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans
      (centralizer_le (show (Z F u).map ι≤W₀ from le_sup_left)))
  have hcenter (v : Vertex F) (hv : (graph F).Adj β v)
      (hvc : (Z F v).map ι≤centralizer (R:Set G)) :
      (Z F v).map ι≤centralizer (Δ:Set G) := by
    have hvV : (Z F v).map ι≤V₁ := map_mono (le_iSup_of_le v
      (le_iSup_of_le ((mem_ball_one F β v).mpr (Or.inl hv)) le_rfl))
    apply le_centralizer_iff.mp
    apply sup_le (le_centralizer_iff.mp hvc)
    intro z hz v hv
    exact hz.2 v (hvV hv)
  have hZaC := hcenter α hab.symm hZaR
  have hZuC := hcenter u hβu hZuR
  have hRne : R≠⊥ := by intro hh; rw [hh,card_bot] at hRcard; contradiction
  obtain ⟨r,hr,hr1⟩ := R.bot_or_exists_ne_one.resolve_left hRne
  have hrZa : r∉(Z F α).map ι := fun hz => hr1 (disjoint_def.mp hdis hr (hZaC hz))
  have hrZu : r∉(Z F u).map ι := fun hz => hr1 (disjoint_def.mp hdis hr (hZuC hz))
  refine ⟨g,hg,hgt,hRcard,hΔcard,hΔiso,?_⟩
  intro y hy hyne hJne
  let : Finite R := Nat.finite_of_card_ne_zero (by rw [hRcard]; decide)
  let J := R⊓(Q F y).map ι
  let : Finite J := Finite.of_injective (inclusion (show J≤R from inf_le_left))
    (inclusion_injective _)
  have hRy : R≤(Q F y).map ι := by
    have hj : 1<Nat.card J := J.one_lt_card_iff_ne_bot.mpr hJne
    have heq : J=R := eq_of_le_of_card_ge inf_le_left (by rw [hRcard]; omega)
    exact heq ▸ (show J≤(Q F y).map ι from inf_le_right)
  obtain ⟨s,hs,hsu⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) β ⟨α,hab.symm⟩ ⟨u,hβu⟩
  change s • α=u at hsu
  have hsβ : s • β=β := sylowGenerated_le _ hs
  have hsp : (graph F).Adj α (s⁻¹ • y) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F s⁻¹).map_adj_iff.mpr hy
    change (graph F).Adj (s⁻¹ • u) (s⁻¹ • y) at hh
    simpa only [←hsu,inv_smul_smul] using hh
  have hspne : s⁻¹ • y≠β := by
    intro he
    have hh := congrArg (s • ·) he
    rw [smul_inv_smul,hsβ] at hh
    exact hyne hh
  have hDeq : D F β t=D F β (s⁻¹ • y) := by
    exact (c.D_eq_neighbor_core_intersection H (reduced_kernel_sylow h) hb ht htne).trans
      (c.D_eq_neighbor_core_intersection H (reduced_kernel_sylow h) hb hsp hspne).symm
  have hDs : (D F β t).map (MulAut.conj s).toMonoidHom=D F β y := by
    rw [hDeq]
    change (Q F β⊓Q F (s⁻¹ • y)).map (MulAut.conj s).toMonoidHom=Q F β⊓Q F y
    rw [map_inf _ _ _ (MulAut.conj s).injective,←Q_translate,←Q_translate,hsβ,smul_inv_smul]
  have image_conj (A : Subgroup (G₀ L S)) (s : G₀ L S) :
      (A.map ι).map (MulAut.conj (ι s)).toMonoidHom=
        (A.map (MulAut.conj s).toMonoidHom).map ι := by
    rw [map_map,map_map]
    congr 1
  have hDs' : D₀.map (MulAut.conj (ι s)).toMonoidHom=Q₁⊓(Q F y).map ι := by
    rw [←hDm,image_conj,hDs]
    change (Q F β⊓Q F y).map ι=_
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hrD' : r∈D₀.map (MulAut.conj (ι s)).toMonoidHom := hDs'.symm ▸ ⟨hRβ hr,hRy hr⟩
  obtain ⟨r',hr'D,hr'eq⟩ := hrD'
  change ι s*r'*(ι s)⁻¹=r at hr'eq
  have hr'Za : r'∉(Z F α).map ι := by
    intro hh
    have hm := mem_map_of_mem (MulAut.conj (ι s)).toMonoidHom hh
    rw [image_conj,←Z_translate,hsu] at hm
    change ι s*r'*(ι s)⁻¹∈(Z F u).map ι at hm
    exact hrZu (hr'eq ▸ hm)
  obtain ⟨q,hq,hqr⟩ := original_bTwo_binary_D_conjugacy h hc hne hb hβu ht htne e hK hD
    r hr.1 hrZa r' hr'D hr'Za
  have hqm : q∈(Q F α).map ι := (reduced_base_Q_map h false).symm ▸ hq
  obtain ⟨q₀,hq₀,rfl⟩ := hqm
  have hQαβ : Q F α≤stabilizer F β :=
    (source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F hab).trans inf_le_right)
  have hQαL : Q F α≤graphLocalGroup F β :=
    pGroup_le_sylowGenerated _ _ hQαβ (isPGroup_pCoreIn 2 _)
  let x₀ := s*q₀
  have hx₀ : x₀∈graphLocalGroup F β := (graphLocalGroup F β).mul_mem hs (hQαL hq₀)
  have hxmove : x₀ • α=u := by
    rw [show x₀=s*q₀ from rfl,mul_smul,Q_le_stabilizer F α hq₀,hsu]
  have hxfix : ι x₀*r*(ι x₀)⁻¹=r := by
    change ι (s*q₀)*r*(ι (s*q₀))⁻¹=r
    rw [map_mul]
    calc
      _=ι s*(ι q₀*r*(ι q₀)⁻¹)*(ι s)⁻¹ := by group
      _=ι s*r'*(ι s)⁻¹ := by rw [hqr]
      _=r := hr'eq
  have hRcyc : R=zpowers r := by
    have hr2 : r^2=1 := by
      have hh := pow_card_eq_one' (x:=(⟨r,hr⟩:R))
      rw [hRcard] at hh
      exact congrArg Subtype.val hh
    exact (eq_of_le_of_card_ge (zpowers_le.mpr hr) (by
      rw [Nat.card_zpowers,orderOf_eq_prime hr2 hr1,hRcard])).symm
  have hxnorm : ι x₀∈normalizer (R:Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change R.map (MulAut.conj (ι x₀)).toMonoidHom=R
    rw [hRcyc,MonoidHom.map_zpowers]
    exact congrArg zpowers hxfix
  have hxL : ι x₀∈enlargedEndpoint L S 1 := by
    have hh := mem_map_of_mem ι hx₀
    rwa [reduced_graphLocalGroup_image h true] at hh
  obtain ⟨a,ha,hxa,hcoset⟩ := hcorrect (ι x₀) hxL hxnorm
  have ham : a∈(Q F α).map ι := (reduced_base_Q_map h false).symm ▸ hRQ ha
  obtain ⟨a₀,ha₀,rfl⟩ := ham
  refine ⟨x₀*a₀,(graphLocalGroup F β).mul_mem hx₀ (hQαL ha₀),?_,?_,?_⟩
  · rw [mul_smul,Q_le_stabilizer F α ha₀,hxmove]
  · simpa only [map_mul] using hxa
  · intro hh
    have hxQ : ι x₀∈Q₁ := hcoset.mp (by simpa only [map_mul] using hh)
    have hxQ' : x₀∈Q F β := by
      have hm : ι x₀∈(Q F β).map ι := (reduced_base_Q_map h true).symm ▸ hxQ
      exact (mem_map_iff_mem (G₀ L S).subtype_injective).mp hm
    have hfix : x₀ • α=α :=
      ((source_Z_Q_U H β).2.trans ((ballKernel_one_le_edge F hab.symm).trans inf_le_right)) hxQ'
    have hdist := hc.1
    rw [←hxmove,hfix,SimpleGraph.dist_self,hb] at hdist
    contradiction

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
