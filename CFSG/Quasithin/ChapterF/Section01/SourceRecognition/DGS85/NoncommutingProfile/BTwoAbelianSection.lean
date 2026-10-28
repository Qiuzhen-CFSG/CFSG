module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSectionIntersections

/-!
# The abelian supplement from a proper beta section

In the equal-field case of DGS (10.10)(d), intersect a proper beta-invariant
section N and its opposite alpha conjugate with Q_alpha. Their intersections
with D_alpha are the two disjoint neighboring center lines, so the two
factors commute and have trivial intersection. Their product W satisfies
W D_alpha = Q_alpha and W intersect D_alpha = Z_alpha.

The actual alpha quotient images of N and its conjugate generate the local
actor. Relative commutators therefore make W invariant. The existing natural
coordinates on Q_alpha/D_alpha restrict to W/Z_alpha. The nonbinary natural
central-extension commutator theorem makes W abelian. Its literal direct
product factors give order q_beta^4.

The original F1.11 application derives every section and image premise from
the proper invariant beta section, retaining its full stabilizer normality,
the opposite conjugator, and the reduced-to-original inclusion. The remaining
radius-two-kernel contradiction is not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(d), printed p.165, using (5.17), p.117, and (10.7), pp.158--159.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k E : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup E] [Module (ZMod 2) E]

private theorem conjugate_le (L A : Subgroup G) (hA : A ≤ L) (g : L) :
    A.map (MulAut.conj (g : G)).toMonoidHom ≤ L := by
  rintro _ ⟨a,ha,rfl⟩
  exact L.mul_mem (L.mul_mem g.property (hA ha)) (L.inv_mem g.property)

private theorem quotient_conjugate (L A : Subgroup G) (hA : A ≤ L)
    {J : Type*} [Group J] (π : L →* J) (g : L) :
    ((A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L).map π =
      ((A.subgroupOf L).map π).map (MulAut.conj (π g)).toMonoidHom := by
  have hc : (A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L =
      (A.subgroupOf L).map (MulAut.conj g).toMonoidHom := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugate_le L A hA g),map_map]
    have he : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp L.subtype := by ext a; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hA]
  rw [hc,map_map,map_map]
  congr 1
  ext a
  exact π.map_mul _ _ |>.trans (by rw [map_mul,map_inv]; rfl)

/-- A beta-invariant section escaping the alpha core fills the literal
Sylow image in the marked alpha quotient. -/
theorem BTwoCenterActionData.invariant_section_image
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k E)
    (N : Subgroup G) (hNQ : N≤Q F m)
    (hPN : stabilizer F m≤normalizer (N:Set G)) (hescape : ¬N≤Q F v) :
    (N.subgroupOf c.actor).map c.quotient=c.imageSylow := by
  have hNL := hNQ.trans c.neighbor_core_le
  apply Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant
    c.imageSylow _
  · exact (map_mono (comap_mono hNQ)).trans_eq c.neighbor_image
  · intro hz
    have hh := (Subgroup.map_eq_bot_iff _).mp hz
    rw [c.kernel] at hh
    have hm := map_mono (f:=c.actor.subtype) hh
    rw [map_subgroupOf_eq_of_le hNL,map_subgroupOf_eq_of_le c.core_le] at hm
    exact hescape hm
  · intro x hx
    obtain ⟨a,rfl⟩ := c.onto x
    have ha : (a:G)∈stabilizer F m := c.normalizer_fixes_neighbor h a hx
    have han : a∈normalizer (N.subgroupOf c.actor:Set c.actor) :=
      le_normalizer_comap c.actor.subtype (hPN ha)
    exact le_normalizer_map c.quotient (mem_map_of_mem c.quotient han)

/-- The two conjugate section intersections commute, supplement the actual
D subgroup, and form a subgroup invariant under the alpha actor. -/
theorem BTwoCenterActionData.section_pair
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    (hb : b F=2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k E)
    (hactor : c.actor=graphLocalGroup F v)
    (hcentral : Z F m≤centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (htne : t≠m)
    (N : Subgroup G) (hNQ : N≤Q F m)
    (hPN : stabilizer F m≤normalizer (N:Set G))
    (hND : N⊓D F m t=Z F m)
    (hI : (N⊓Q F v)⊔D F m t=Q F v⊓Q F m)
    (himage : (N.subgroupOf c.actor).map c.quotient=c.imageSylow)
    (hgen : (Q F v⊓Q F m)⊔(Q F v⊓Q F t)=Q F v)
    (g : c.actor) (hg : (g:G) • m=t)
    (hop : c.quotient g∉normalizer (c.imageSylow:Set SL(2,k))) :
    let N' := N.map (MulAut.conj (g:G)).toMonoidHom
    let A := N⊓Q F v
    let A' := N'⊓Q F v
    let W := A⊔A'
    Disjoint N N' ∧ A≤centralizer (A':Set G) ∧
      W≤Q F v ∧ W⊓D F m t=Z F v ∧ W⊔D F m t=Q F v ∧
      c.actor≤normalizer (W:Set G) := by
  let := finite_endpoints h
  let hS := source_kernel_sylow h hB hSyl
  let f := (MulAut.conj (g:G)).toMonoidHom
  let N' := N.map f
  let A := N⊓Q F v
  let A' := N'⊓Q F v
  let W := A⊔A'
  have hgv : (g:G) • v=v := c.actor_le g.property
  have hQmap : (Q F v).map f=Q F v := by rw [←Q_translate,hgv]
  have hDnorm := c.D_stabilizer_normalized h hS hb ht htne
  have hDmap : (D F m t).map f=D F m t :=
    mem_normalizer_iff_map_conj_eq.mp (hDnorm (c.actor_le g.property))
  have hN'Q : N'≤Q F t := by
    have hh := map_mono (f:=f) hNQ
    change N'≤(Q F m).map (MulAut.conj (g:G)).toMonoidHom at hh
    rwa [←Q_translate,hg] at hh
  have hN'D : N'⊓D F m t=Z F t := by
    have hh := congrArg (map f) hND
    rwa [map_inf _ _ _ (MulAut.conj (g:G)).injective,hDmap,←Z_translate,hg] at hh
  obtain ⟨hZspan,hZdis⟩ := c.central_neighbor_centers h hB hSyl hb hactor hcentral ht htne
  have hNN' : Disjoint N N' := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxD : x∈D F m t := ⟨hNQ hx.1,hN'Q hx.2⟩
    exact (disjoint_iff.mp hZdis) ▸ (show x∈Z F m⊓Z F t from
      ⟨hND ▸ ⟨hx.1,hxD⟩,hN'D ▸ ⟨hx.2,hxD⟩⟩)
  have hQvM : Q F v≤stabilizer F m :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F c.middle).trans inf_le_right)
  have hQvT : Q F v≤stabilizer F t :=
    (source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F ht).trans inf_le_right)
  have hPN' : stabilizer F t≤normalizer (N':Set G) := by
    intro x hx
    have hx' : (g:G)⁻¹*x*(g:G)∈stabilizer F m := by
      change ((g:G)⁻¹*x*(g:G)) • m=m
      rw [mul_smul,mul_smul,hg,show x • t=t from hx,←hg,inv_smul_smul]
    have hn := mem_normalizer_iff_map_conj_eq.mp (hPN hx')
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (N.map f).map (MulAut.conj x).toMonoidHom=N.map f
    have hh := congrArg (map f) hn
    simp only [map_map] at hh ⊢
    have he : f.comp (MulAut.conj ((g:G)⁻¹*x*(g:G))).toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp f := by
      ext z
      simp [f,MulAut.conj_apply,mul_assoc]
    exact (congrArg (fun q : G→*G => N.map q) he).symm.trans hh
  have hnA : Q F v≤normalizer (A:Set G) :=
    (le_inf (hQvM.trans hPN) (Q F v).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hnA' : Q F v≤normalizer (A':Set G) :=
    (le_inf (hQvT.trans hPN') (Q F v).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcAB : A≤centralizer (A':Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply le_trans _ (disjoint_iff.mp hNN').le
    apply le_inf
    · exact (le_normalizer_iff_commutator_le_left.mp
        (show A'≤normalizer (A:Set G) from inf_le_right.trans hnA)).trans inf_le_left
    · rw [commutator_comm]
      exact (le_normalizer_iff_commutator_le_left.mp
        (show A≤normalizer (A':Set G) from inf_le_right.trans hnA')).trans inf_le_left
  have hWQ : W≤Q F v := sup_le inf_le_right inf_le_right
  have hAmap : A.map f=A' := by rw [map_inf _ _ _ (MulAut.conj (g:G)).injective,hQmap]
  have hI' : A'⊔D F m t=Q F v⊓Q F t := by
    have hh := congrArg (map f) hI
    change (A⊔D F m t).map f=_ at hh
    rwa [Subgroup.map_sup,hAmap,hDmap,map_inf _ _ _ (MulAut.conj (g:G)).injective,
      hQmap,←Q_translate,hg] at hh
  have hWD : W⊔D F m t=Q F v := by
    rw [←hgen,←hI,←hI']
    change (A⊔A')⊔D F m t=(A⊔D F m t)⊔(A'⊔D F m t)
    calc (A⊔A')⊔D F m t = (A⊔A')⊔(D F m t⊔D F m t) := by rw [sup_idem]
         _ = _ := sup_sup_sup_comm _ _ _ _
  have hZD : Z F v≤D F m t := by
    obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
    exact (d.decomposition h hS hb) ▸ le_sup_left
  have hZWA : Z F m≤A := le_inf (hND ▸ inf_le_left)
    ((hZspan ▸ le_sup_left).trans (fun _ hz => ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).1))
  have hZWB : Z F t≤A' := le_inf (hN'D ▸ inf_le_left)
    ((hZspan ▸ le_sup_right).trans (fun _ hz => ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).1))
  have hWint : W⊓D F m t=Z F v := by
    apply le_antisymm ?_ (le_inf (hZspan ▸ sup_le (hZWA.trans le_sup_left) (hZWB.trans le_sup_right)) hZD)
    intro x hx
    have hxprod : x∈(A:Set G)*(A':Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _
        (hcAB.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx.1
    obtain ⟨a,ha,b,hb',rfl⟩ := hxprod
    have hbM : b∈Q F m := by
      simpa only [inv_mul_cancel_left] using
        (Q F m).mul_mem ((Q F m).inv_mem (hNQ ha.1)) hx.2.1
    have hbD : b∈D F m t := ⟨hbM,hN'Q hb'.1⟩
    have haD : a∈D F m t := by
      simpa only [mul_inv_cancel_right] using (D F m t).mul_mem hx.2 ((D F m t).inv_mem hbD)
    rw [hZspan]
    exact (Z F m⊔Z F t).mul_mem (mem_sup_left (hND ▸ ⟨ha.1,haD⟩))
      (mem_sup_right (hN'D ▸ ⟨hb'.1,hbD⟩))
  have hNL : N≤c.actor := hNQ.trans c.neighbor_core_le
  have hN'L : N'≤c.actor := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := hx
    exact c.actor.mul_mem (c.actor.mul_mem g.property (hNL hn)) (c.actor.inv_mem g.property)
  have hN'im : (N'.subgroupOf c.actor).map c.quotient=
      (c.imageSylow:Subgroup SL(2,k)).map (MulAut.conj (c.quotient g)).toMonoidHom := by
    rw [quotient_conjugate c.actor N hNL c.quotient g,himage]
  have hLgen : (N⊔N')⊔Q F v=c.actor := by
    let J := (N⊔N')⊔Q F v
    have hJL : J≤c.actor := sup_le (sup_le hNL hN'L) c.core_le
    have him : (J.subgroupOf c.actor).map c.quotient=⊤ := by
      rw [subgroupOf_sup (sup_le hNL hN'L) c.core_le,subgroupOf_sup hNL hN'L,
        Subgroup.map_sup,Subgroup.map_sup,himage,hN'im,
        Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer c.imageSylow hop,top_sup_eq]
    have he : J.subgroupOf c.actor=⊤ := map_injective_of_ker_le c.quotient
      (by rw [c.kernel]; exact comap_mono le_sup_right) le_top
      (him.trans (map_top_of_surjective c.quotient c.onto).symm)
    have hh := congrArg (map c.actor.subtype) he
    rwa [map_subgroupOf_eq_of_le hJL,←MonoidHom.range_eq_map,range_subtype] at hh
  have hnW : Q F v≤normalizer (W:Set G) :=
    (le_inf hnA hnA').trans (normalizer_inf_normalizer_le_normalizer_sup A A')
  have hcomm (T : Subgroup G) (hTL : T≤c.actor) (hnT : Q F v≤normalizer (T:Set G)) :
      ⁅W,T⁆≤T⊓Q F v := by
    apply le_inf
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp (hWQ.trans hnT)
    · exact (commutator_mono hWQ le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hTL.trans (c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F v))))
  refine ⟨hNN',hcAB,hWQ,hWint,hWD,?_⟩
  apply hLgen.ge.trans
  apply sup_le (sup_le ?_ ?_) hnW
  · exact le_normalizer_iff_commutator_le_left.mpr ((hcomm N hNL (hQvM.trans hPN)).trans le_sup_left)
  · exact le_normalizer_iff_commutator_le_left.mpr ((hcomm N' hN'L (hQvT.trans hPN')).trans le_sup_right)


local instance sectionPairAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

open Matrix in
/-- A normalized supplement with precisely the natural center in its kernel
is abelian: its quotient inherits the already constructed natural core layers. -/
theorem BTwoCenterActionData.natural_supplement_commutative
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    (hb : b F=2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k E)
    (hactor : c.actor=graphLocalGroup F v)
    (hcentral : Z F m≤centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (htne : t≠m)
    (hcomm : ⁅V F m 1,Q F m⁆≤Z F m)
    (hnot : ¬stabilizer F v≤normalizer ((Q F m⊓Q F v:Subgroup G):Set G))
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (eβ : (graphLocalGroup F m⧸pCore 2 (graphLocalGroup F m))≃*SL(2,K))
    (Ec : E≃ₗ[ZMod 2](Fin 2→k)) (hk : 2<Nat.card k)
    (W : Subgroup G) (hWQ : W≤Q F v) (hWD : W⊓D F m t=Z F v)
    (hgen : W⊔D F m t=Q F v) (hnW : c.actor≤normalizer (W:Set G)) :
    IsMulCommutative W := by
  classical
  obtain ⟨hN,hE,σ,d,_,_,n,e,he⟩ := c.linear_core_natural_copies h hB hSyl hb hactor
    hcentral ht htne hcomm hnot eβ
  let _ := hN
  let _ := hE
  obtain ⟨eZ,heZ⟩ := c.center_natural_coordinates Ec
  let f := e.toAddEquiv.toMultiplicative.toMonoidHom.comp
    (d.coordinates.comp (inclusion hWQ))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := d.onto (e.toAddEquiv.toMultiplicative.symm y)
    have hnD := c.D_stabilizer_normalized h (source_kernel_sylow h hB hSyl) hb ht htne
    have hxp : (x:G)∈(W:Set G)*(D F m t:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (hWQ.trans ((Q_le_stabilizer F v).trans hnD)),hgen]
      exact x.property
    obtain ⟨a,ha,b,hb',hxprod⟩ := hxp
    let a' : W := ⟨a,ha⟩
    have hbQ : b∈Q F v := d.kernel_le hb'
    let b' : Q F v := ⟨b,hbQ⟩
    have hx' : x=inclusion hWQ a'*b' := Subtype.ext hxprod.symm
    have hd : d.coordinates (inclusion hWQ a')=e.toAddEquiv.toMultiplicative.symm y := by
      rw [hx',map_mul,(d.coordinates_eq_one_iff b').mpr hb',mul_one] at hx
      exact hx
    exact ⟨a',by change e.toAddEquiv.toMultiplicative (d.coordinates (inclusion hWQ a'))=y
                 rw [hd,e.toAddEquiv.toMultiplicative.apply_symm_apply]⟩
  have hker (x : W) : x∈f.ker ↔ (x:G)∈Z F v := by
    change e.toAddEquiv.toMultiplicative (d.coordinates (inclusion hWQ x))=1 ↔ _
    rw [←e.toAddEquiv.toMultiplicative.map_one,e.toAddEquiv.toMultiplicative.injective.eq_iff,
      d.coordinates_eq_one_iff]
    exact ⟨fun hx => hWD ▸ ⟨x.property,hx⟩,fun hx => (hWD.symm ▸ hx).2⟩
  have hcz : f.ker≤center W := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (graph_Q_centralizes_Z h v (hWQ y.property) x ((hker x).mp hx)).symm
  let j : f.ker→*Z F v := {
    toFun x := ⟨((x:W):G),(hker x).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y hh
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : Z F v => (z:G)) hh
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  have hci : Function.Injective c.coordinates.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.coordinates.kernel_eq,hω,bot_subgroupOf]
  let z := eZ.toAddEquiv.toMultiplicative.toMonoidHom.comp (c.coordinates.coordinates.comp j)
  have hzi : Function.Injective z := eZ.toAddEquiv.toMultiplicative.injective.comp (hci.comp hj)
  obtain ⟨a,ha0,ha1⟩ : ∃ a:k,a≠0 ∧ a≠1 := by
    by_contra! hn
    have hcard : Nat.card k≤2 := by
      let := Fintype.ofFinite k
      rw [Nat.card_eq_fintype_card]
      calc Fintype.card k = (Finset.univ:Finset k).card := rfl
           _ ≤ ({0,1}:Finset k).card := Finset.card_le_card (by
             intro x _
             by_cases hx:x=0
             · simp [hx]
             · simp [hn x hx])
           _ ≤ 2 := by simp
    omega
  let φ := W.normalizerMonoidHom.comp (inclusion hnW)
  apply Representation.SL2.commutative_of_natural_central_extension a ha0 ha1 f hf hcz z hzi
    c.quotient c.onto φ
  · intro g x
    change e (d.coordinates (inclusion hWQ (φ g x))).toAdd=_
    have hh : inclusion hWQ (φ g x)=c.coreConjugation g (inclusion hWQ x) := rfl
    rw [hh]
    have hde := d.equivariant g (inclusion hWQ x)
    change (d.coordinates (c.coreConjugation g (inclusion hWQ x))).toAdd=
      σ (c.quotient g) (d.coordinates (inclusion hWQ x)).toAdd at hde
    rw [hde]
    funext i
    exact he (c.quotient g) (d.coordinates (inclusion hWQ x)).toAdd i
  · intro g x y hxy
    change eZ (c.coordinates.coordinates (j y)).toAdd=
      (c.quotient g).val *ᵥ eZ (c.coordinates.coordinates (j x)).toAdd
    rw [←heZ]
    congr 1
    have hjy : j y=⟨(g:G)*(j x:G)*(g:G)⁻¹,
        (mem_normalizer_iff.mp (c.coordinates.normalized g.property) (j x)).mp (j x).property⟩ := by
      apply Subtype.ext
      exact (congrArg (fun q:W => (q:G)) hxy).symm
    rw [hjy]
    exact c.coordinates.equivariant g (j x)


namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The abelian subgroup constructed from a proper invariant beta section
in DGS p.165, with the original conjugator and core maps. -/
theorem original_bTwo_proper_section_abelian_supplement
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι≠(Z F₀ α).map ι)
    (N : Subgroup G) (hNQ : N<(parabolic L S 1).pCoreIn 2)
    (hZN : (Z F₀ β).map ι<N) (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    ∃ g : G₀ L S, g∈graphLocalGroup F₀ α ∧ g • β=t ∧
      let N' := N.map (MulAut.conj (g:G)).toMonoidHom
      let A := N⊓(parabolic L S 0).pCoreIn 2
      let A' := N'⊓(parabolic L S 0).pCoreIn 2
      let W := A⊔A'
      Disjoint N N' ∧ A≤centralizer (A':Set G) ∧
        IsMulCommutative W ∧ Nat.card W=Nat.card (K true)^4 ∧
        W⊓((parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι)=(Z F₀ α).map ι ∧
        W⊔((parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι)=(parabolic L S 0).pCoreIn 2 ∧
        enlargedEndpoint L S 0≤normalizer (W:Set G) := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F₀ i) := finite_endpoints H
  have hab : (graph F₀).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let hB := reduced_borel_core_sylow h
  let hSyl := reduced_vertex_sylow h
  let hS := reduced_kernel_sylow h
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let eβ := (reduced_graphLinearQuotient h true (e true)).trans
    (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL (K true)).symm
  obtain ⟨heq,hNZ,hND,hAc,hescape⟩ :=
    original_bTwo_nonbinary_beta_proper_core_intersection h hc hne hb hβu ht htne K e hK hD N hNQ hZN hPN
  obtain ⟨hZD,hDQ,_,_,hZb,_⟩ := original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  rw [heq] at hZb
  let N₀ := N.subgroupOf (G₀ L S)
  let A := N₀⊓Q F₀ α
  let I := Q F₀ α⊓Q F₀ β
  have hN0 : N≤G₀ L S := hNQ.le.trans ((reduced_base_Q_map h true).ge.trans (map_subtype_le _))
  have hNm : N₀.map ι=N := map_subgroupOf_eq_of_le hN0
  have hQa : (Q F₀ α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F₀ β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hDm : (D F₀ β t).map ι=(parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι := by
    rw [D,map_inf _ _ _ (G₀ L S).subtype_injective,hQb]
  have hAm : A.map ι=N⊓(parabolic L S 0).pCoreIn 2 := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hNm,hQa]
  have hAc₀ : Nat.card A=Nat.card (K true)^2 := by
    rw [←card_map_of_injective (f:=ι) (G₀ L S).subtype_injective,hAm,hAc]
  have hZbc : Nat.card (Z F₀ β)=Nat.card (K true) := by
    rwa [card_map_of_injective (G₀ L S).subtype_injective] at hZb
  have hkc : Nat.card k=Nat.card (K true) :=
    (c.central_middle_center_card H hB hSyl hb hactor hcentral (LinearEquiv.refl _ _)).symm.trans hZbc
  have hNQ₀ : N₀≤Q F₀ β := by
    apply (map_le_map_iff_of_injective (f:=ι) (G₀ L S).subtype_injective).mp
    rw [hNm,hQb]
    exact hNQ.le
  have hPN₀ : stabilizer F₀ β≤normalizer (N₀:Set (G₀ L S)) := by
    intro x hx
    have hxP : (x:G)∈P₀ L S 1 := by
      rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hx
      exact hx
    exact le_normalizer_comap ι (hPN (P₀_le h 1 hxP))
  have hND₀ : N₀⊓D F₀ β t=Z F₀ β := by
    apply map_injective (G₀ L S).subtype_injective
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hNm,hDm]
    exact hND
  have hDQ₀ : D F₀ β t≤Q F₀ α := by
    apply (map_le_map_iff_of_injective (f:=ι) (G₀ L S).subtype_injective).mp
    rw [hDm,hQa]
    exact hDQ
  have hesc₀ : ¬N₀≤Q F₀ α := by
    intro hh
    apply hescape
    simpa only [hNm,hQa] using map_mono (f:=ι) hh
  have hIidx : (D F₀ β t).relIndex I=Nat.card (K true) :=
    c.linear_seed_factor_index H hB hSyl hS hb ht htne hnot eβ
  have hDI : D F₀ β t≤I := le_inf hDQ₀ inf_le_left
  have hAI : A≤I := le_inf inf_le_right (inf_le_left.trans hNQ₀)
  have hnA : Q F₀ α≤normalizer (A:Set (G₀ L S)) :=
    (le_inf (((source_Z_Q_U H α).2.trans ((ballKernel_one_le_edge F₀ hab).trans inf_le_right)).trans hPN₀)
      (Q F₀ α).le_normalizer).trans inf_normalizer_le_normalizer_inf
  let : Finite (Q F₀ α) := Finite.of_injective (inclusion (Q_le_stabilizer F₀ α)) (inclusion_injective _)
  let : Finite I := Finite.of_injective (inclusion (show I≤Q F₀ α from inf_le_left)) (inclusion_injective _)
  let : Finite (D F₀ β t) := Finite.of_injective (inclusion hDQ₀) (inclusion_injective _)
  have hAD : A⊓D F₀ β t=Z F₀ β := by
    change (N₀⊓Q F₀ α)⊓D F₀ β t=_
    rw [inf_assoc,inf_eq_right.mpr hDQ₀,hND₀]
  have hiA : (D F₀ β t).relIndex A=Nat.card (K true) := by
    have hh := relIndex_mul_card_of_le (show A⊓D F₀ β t≤A from inf_le_left)
    rw [inf_relIndex_left,hAD,hAc₀,hZbc,pow_two] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hh
  have hI : A⊔D F₀ β t=I := by
    apply eq_of_le_of_card_ge (sup_le hAI hDI)
    have hi := relIndex_mul_card_of_le (show D F₀ β t≤A⊔D F₀ β t from le_sup_right)
    rw [relIndex_sup_of_normalizes A (D F₀ β t) (hDQ₀.trans hnA),hiA] at hi
    have hj := relIndex_mul_card_of_le hDI
    rw [hIidx] at hj
    exact (hj.symm.trans hi).le
  have himage := c.invariant_section_image H N₀ hNQ₀ hPN₀ hesc₀
  have hgen : (Q F₀ α⊓Q F₀ β)⊔(Q F₀ α⊓Q F₀ t)=Q F₀ α :=
    (c.seed_eq_core_intersections H hS hb ht htne).symm.trans
      (c.linear_seed_eq_core_and_index H hB hSyl hS hb ht htne hnot eβ).1
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift H ht htne
  let N₁ := N₀.map (MulAut.conj (g:G₀ L S)).toMonoidHom
  let A' := N₁⊓Q F₀ α
  let W := A⊔A'
  obtain ⟨hdis,hpair,hWQ,hWint,hWsup,hnW⟩ := c.section_pair H hB hSyl hb hactor hcentral
    ht htne N₀ hNQ₀ hPN₀ hND₀ hI himage hgen g hg hop
  change Disjoint N₀ N₁ at hdis
  change A≤centralizer (A':Set (G₀ L S)) at hpair
  change W≤Q F₀ α at hWQ
  change W⊓D F₀ β t=Z F₀ α at hWint
  change W⊔D F₀ β t=Q F₀ α at hWsup
  change c.actor≤normalizer (W:Set (G₀ L S)) at hnW
  have habel : IsMulCommutative W := c.natural_supplement_commutative H hB hSyl hb hactor hcentral
    ht htne hcomm.le hnot eβ (LinearEquiv.refl _ _) (hkc.symm ▸ hK) W hWQ hWint hWsup hnW
  have hA'conj : A'=A.map (MulAut.conj (g:G₀ L S)).toMonoidHom := by
    rw [map_inf _ _ _ (MulAut.conj (g:G₀ L S)).injective,←Q_translate,
      show (g:G₀ L S) • α=α from c.actor_le g.property]
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A A'
    (hdis.mono inf_le_left inf_le_left) hpair
  have hWcard : Nat.card W=Nat.card (K true)^4 := by
    rw [←Nat.card_congr ep.toEquiv,Nat.card_prod,hA'conj,card_map_of_injective (MulAut.conj (g:G₀ L S)).injective,hAc₀]
    ring
  let g₀ : G₀ L S := g
  have hN₁m : N₁.map ι=N.map (MulAut.conj (g₀:G)).toMonoidHom := by
    rw [map_map,←hNm,map_map]
    rfl
  have hA'm : A'.map ι=(N.map (MulAut.conj (g₀:G)).toMonoidHom)⊓(parabolic L S 0).pCoreIn 2 := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,hN₁m,hQa]
  let W₀ := (N⊓(parabolic L S 0).pCoreIn 2)⊔
    ((N.map (MulAut.conj (g₀:G)).toMonoidHom)⊓(parabolic L S 0).pCoreIn 2)
  have hWm : W.map ι=W₀ := by rw [Subgroup.map_sup,hAm,hA'm]
  refine ⟨g₀,hactor ▸ g.property,hg,?_,?_,?_,?_,?_,?_,?_⟩
  · apply disjoint_iff.mpr
    have hh := congrArg (map ι) (disjoint_iff.mp hdis)
    simpa only [map_inf _ _ _ (G₀ L S).subtype_injective,hNm,hN₁m,Subgroup.map_bot] using hh
  · apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (map ι) (commutator_eq_bot_iff_le_centralizer.mpr hpair)
    simpa only [map_commutator,hAm,hA'm,Subgroup.map_bot] using hh
  · let _ := habel
    let ee := (W.equivMapOfInjective ι (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr hWm)
    refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨a,rfl⟩ := ee.surjective x
    obtain ⟨b,rfl⟩ := ee.surjective y
    rw [←map_mul,←map_mul,mul_comm]
  · change Nat.card W₀=_
    rw [←hWm,card_map_of_injective (G₀ L S).subtype_injective,hWcard]
  · have hh := congrArg (map ι) hWint
    simpa only [map_inf _ _ _ (G₀ L S).subtype_injective,hWm,hDm] using hh
  · have hh := congrArg (map ι) hWsup
    rw [Subgroup.map_sup,hWm,hDm,hQa] at hh
    exact hh
  · have hh := (map_mono (f:=ι) hnW).trans (le_normalizer_map ι)
    change c.actor.map ι≤normalizer (W.map ι:Set G) at hh
    have hLm : c.actor.map ι=enlargedEndpoint L S 0 :=
      (congrArg (map ι) hactor).trans (reduced_graphLocalGroup_image h false)
    rwa [hLm,hWm] at hh

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
