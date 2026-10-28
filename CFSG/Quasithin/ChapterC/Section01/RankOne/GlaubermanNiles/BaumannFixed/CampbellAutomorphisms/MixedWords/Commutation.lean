module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.Core
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.CentralPullback
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.MixedWords.ConjugateFixed

/-!
# Campbell mixed-word commutation on the source actors

The mixed core placement gives two bounds on the inverse-image commutator.
Conjugating by the source involution puts it in two distinct Sylow fixed
layers, whose intersection is central. Natural displacement then forces
commutation. Conjugating this identity by the original involution gives
the two actor identities needed in II.7.2 and II.7.6.
Source: Campbell, Pushing up in Finite Groups, II.6.4(d–f), pp.32–33.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem conjugate_twice (g : H) (hg : g^2=1) (X : Subgroup H) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom=X := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom=MonoidHom.id H := by
    ext x
    change g*(g*x*g⁻¹)*g⁻¹=x
    have hgg : g*g=1 := by simpa only [pow_two] using hg
    calc
      g*(g*x*g⁻¹)*g⁻¹=(g*g)*x*(g*g)⁻¹ := by group
      _=x := by rw [hgg]; simp
  rw [he,Subgroup.map_id]

omit [Finite H] in
private theorem order_two_power (g : H) (hg : g^2=1) : ∃n,orderOf g=2^n := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp (orderOf_dvd_of_pow_eq_one hg) with he | he
  · exact ⟨0,by simpa using he⟩
  · exact ⟨1,by simpa using he⟩

theorem InLocalClass.mixed_conjugates_commute
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤)
    (g t : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) (ht : t ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : g^2=1) (ht2 : t^2=1) (htM : t ∉ M) :
    let P := automorphismImage S a.symm
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom)
    ⁅P.map (MulAut.conj t).toMonoidHom,P⁆=⊥ := by
  let Z := Campbell.V H ⊓ centralizer (S : Set H)
  let X := (automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom
  let P := automorphismImage S a.symm X
  let Pt := P.map (MulAut.conj t).toMonoidHom
  let W := automorphismImage S a Pt
  let D := ⁅Pt,P⁆
  let C := ⁅W,X⁆
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  have hQS : pCore 2 H ≤ S := hSd ▸ pCore_isPGroup.le_sylow_of_normal d.sylow
  have hZS : Z ≤ S := inf_le_left.trans (Campbell.V_le_pCore.trans hQS)
  obtain ⟨AX,hAX,_,hXAX⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
  have hXS : X ≤ S := hXAX.trans hAX.1
  obtain ⟨AP,hAP,hAPQ,hPAP⟩ := h.inverse_conjugate_submaximal S hB a (hAll a) g hg (order_two_power g hg2)
  have hPQ : P ≤ pCore 2 H := hPAP.trans hAPQ
  obtain ⟨AT,hAT,_,hPtAT⟩ := h.submaximal_core_conjugate S hB P ⟨AP,hAP,hPAP⟩ hPQ t
  have hPtS : Pt ≤ S := hPtAT.trans hAT.1
  have hWQ : W ≤ pCore 2 H := h.mixed_conjugate_core S hB a hAll hF g t hg ht hg2 ht2
  have hWsub : ∃ A ∈ elementaryAbelianMaxSubgroups S, W ≤ A :=
    ⟨automorphismImage S a AT,automorphismImage_maxElementary S a AT hAT,
      automorphismImage_mono S a hPtAT⟩
  have hWR : W ≤ Campbell.J (pCore 2 H) := h.submaximal_core_le_thompson hB d W
    (automorphismImage S a AT) (hSd.symm ▸ automorphismImage_maxElementary S a AT hAT)
    (automorphismImage_mono S a hPtAT) hWQ
  have hCaZ : C ≤ automorphismImage S a Z := by
    rw [show C=⁅X,W⁆ from commutator_comm W X]
    exact (commutator_mono le_rfl hWR).trans
      (h.automorphism_conjugate_core_commutator S hB a (hAll a) g hg)
  have hDC : automorphismImage S a.symm C=D := by
    rw [automorphismImage_commutator S a.symm W X (automorphismImage_le S a Pt) hXS,
      automorphismImage_symm S a Pt hPtS]
  have hDZ : D ≤ Z := by
    have hi := automorphismImage_mono S a.symm hCaZ
    rw [hDC,automorphismImage_symm S a Z hZS] at hi
    exact hi
  have hDt : D.map (MulAut.conj t).toMonoidHom=D := by
    change (⁅P.map (MulAut.conj t).toMonoidHom,P⁆).map (MulAut.conj t).toMonoidHom=⁅Pt,P⁆
    rw [map_commutator,conjugate_twice t ht2 P,commutator_comm]
  have hDZt : D ≤ Z.map (MulAut.conj t).toMonoidHom := hDt ▸ map_mono hDZ
  have hDcenter : D ≤ center H := (le_inf hDZ hDZt).trans
    (h.fixed_inf_conjugate_le_center S hB M hM t htM)
  have hCzero : C=⊥ := h.automorphism_conjugate_commutes_of_central_pullback S hB a g W hWsub hWQ
    (hCaZ.trans (automorphismImage_le S a Z))
    (hCaZ.trans (h.automorphism_fixed_le_center S hB a (hAll a) hF)) (hDC ▸ hDcenter)
  have hi := congrArg (automorphismImage S a.symm) hCzero
  rw [hDC,automorphismImage_bot S a.symm] at hi
  exact hi

omit [Finite H] in
private theorem conj_map_mul (A : Subgroup H) (x g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj (x*g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply,mul_assoc]

theorem InLocalClass.mixed_conjugate_actor_commutes
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤)
    (g x : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) (hxK : x ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : g^2=1) (hx2 : x^2=1) (hgM : g ∉ M) (hxS : x ∈ S) (hxQ : x ∉ pCore 2 H) :
    let P := automorphismImage S a.symm
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom)
    let Y := P.map (MulAut.conj g).toMonoidHom
    ⁅Y,Y.map (MulAut.conj x).toMonoidHom⁆=⊥ := by
  let P := automorphismImage S a.symm
    ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom)
  let t := (MulAut.conj g) x
  have htK : t ∈ Campbell.J (⊤ : Subgroup H) :=
    (Campbell.J (⊤ : Subgroup H)).mul_mem ((Campbell.J (⊤ : Subgroup H)).mul_mem hg hxK)
      ((Campbell.J (⊤ : Subgroup H)).inv_mem hg)
  have ht2 : t^2=1 := by
    change ((MulAut.conj g) x)^2=1
    rw [←map_pow,hx2,map_one]
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  have hSd : (d.sylow : Subgroup H)=S := hS.trans (range_subtype S)
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  have htM : t ∉ M := h.campbell_maximal_separation hB m d hS M
    (by rw [hSd]; exact hM) g x hgM
    (by change x ∈ (d.sylow : Subgroup H); rwa [hSd]) hxQ
  have hc := h.mixed_conjugates_commute S hB a hAll hF M hM g t hg htK hg2 ht2 htM
  change ⁅P.map (MulAut.conj t).toMonoidHom,P⁆=⊥ at hc
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hc
  rw [map_commutator,Subgroup.map_bot,conj_map_mul] at hm
  have hgt : g*t=x*g := by
    change g*(g*x*g⁻¹)=x*g
    have hgg : g*g=1 := by simpa only [pow_two] using hg2
    have hgi : g⁻¹=g := inv_eq_of_mul_eq_one_left hgg
    calc
      g*(g*x*g⁻¹)=(g*g)*x*g⁻¹ := by group
      _=x*g := by rw [hgg,one_mul,hgi]
  rw [hgt,commutator_comm] at hm
  dsimp only
  rw [conj_map_mul]
  exact hm

theorem InLocalClass.mixed_inverse_actor_commutes
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hF : ¬automorphismImage S a (Campbell.F H) ≤ Campbell.F H)
    (g x : H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) (hxK : x ∈ Campbell.J (⊤ : Subgroup H))
    (hg2 : g^2=1) (hx2 : x^2=1) :
    let P := automorphismImage S a.symm
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom)
    ⁅P.map (MulAut.conj g).toMonoidHom,
      (automorphismImage S a.symm (Campbell.F H)).map (MulAut.conj (x*g)).toMonoidHom⁆=⊥ := by
  let X := (automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom
  let P := automorphismImage S a.symm X
  let t := (MulAut.conj g) x
  let B := (automorphismImage S a.symm (Campbell.F H)).map (MulAut.conj t).toMonoidHom
  have htK : t ∈ Campbell.J (⊤ : Subgroup H) :=
    (Campbell.J (⊤ : Subgroup H)).mul_mem ((Campbell.J (⊤ : Subgroup H)).mul_mem hg hxK)
      ((Campbell.J (⊤ : Subgroup H)).inv_mem hg)
  have ht2 : t^2=1 := by
    change ((MulAut.conj g) x)^2=1
    rw [←map_pow,hx2,map_one]
  obtain ⟨AX,hAX,_,hXAX⟩ := h.automorphism_F_conjugate_submaximal S hB a (hAll a) g
  have hXS : X ≤ S := hXAX.trans hAX.1
  obtain ⟨AB,hAB,_,hBAB⟩ := h.automorphism_F_conjugate_submaximal S hB a.symm (hAll a.symm) t
  have hBS : B ≤ S := hBAB.trans hAB.1
  have hc := h.mixed_inverse_words_commute S hB a hAll hF g t hg htK hg2 ht2
  have hc' := congrArg (automorphismImage S a.symm) hc
  rw [automorphismImage_commutator S a.symm X (automorphismImage S a B)
      hXS (automorphismImage_le S a B),
    automorphismImage_symm S a B hBS,automorphismImage_bot S a.symm] at hc'
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hc'
  rw [map_commutator,Subgroup.map_bot] at hm
  change ⁅P.map (MulAut.conj g).toMonoidHom,B.map (MulAut.conj g).toMonoidHom⁆=⊥ at hm
  change ⁅P.map (MulAut.conj g).toMonoidHom,
    ((automorphismImage S a.symm (Campbell.F H)).map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom⁆=⊥ at hm
  rw [conj_map_mul] at hm
  have hgt : g*t=x*g := by
    change g*(g*x*g⁻¹)=x*g
    have hgg : g*g=1 := by simpa only [pow_two] using hg2
    have hgi : g⁻¹=g := inv_eq_of_mul_eq_one_left hgg
    calc
      g*(g*x*g⁻¹)=(g*g)*x*g⁻¹ := by group
      _=x*g := by rw [hgg,one_mul,hgi]
  rwa [hgt] at hm
end CFSG.Quasithin.ChapterC.GlaubermanNiles
