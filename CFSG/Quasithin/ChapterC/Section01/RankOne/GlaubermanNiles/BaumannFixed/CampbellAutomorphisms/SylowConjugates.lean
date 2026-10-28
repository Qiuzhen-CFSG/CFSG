module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.ActorMovement
/-!
# Campbell II.6.3 for every original Sylow conjugator

Assume V^α≤O₂(H) for α∈Aut(S). If two J(H)-conjugates of F^α related by
t∈S∩J(H) failed to commute, transport their relative conjugator back through
α. The resulting natural actor moves F and therefore supplements O₂(H).
The two-core normalizes each F^α-conjugate, so factor t as an actor times a
core element. The actual full-actor commutation theorem gives the desired
contradiction. If F^α≤F, both conjugates lie in the normal elementary F.
This discharges the arbitrary-Sylow-representative step without adding a
factorization, fixed-point or module witness to the original local input.
Source: Campbell, *Pushing up in Finite Groups*, II.6.3, printed pp.30–31.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem conj_map_mul (A : Subgroup H) (x g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj (x*g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply,mul_assoc]

theorem InLocalClass.sylow_conjugates_commute (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (a : MulAut S) (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (t g : H) (ht : t ∈ S) (htK : t ∈ Campbell.J (⊤ : Subgroup H))
    (hg : g ∈ Campbell.J (⊤ : Subgroup H)) :
    let Y := automorphismImage S a (Campbell.F H)
    ⁅Y.map (MulAut.conj g).toMonoidHom,Y.map (MulAut.conj (t*g)).toMonoidHom⁆=⊥ := by
  let Y := automorphismImage S a (Campbell.F H)
  let K := Campbell.J (⊤ : Subgroup H)
  let W := conjugateSpanBy Y K
  let W' := automorphismImage S a.symm W
  let A := Y.map (MulAut.conj g).toMonoidHom
  by_cases hF : Y ≤ Campbell.F H
  · have hA : A ≤ Campbell.F H := by
      rintro z ⟨y,hy,rfl⟩
      exact (Campbell.F_normal).conj_mem y (hF hy) g
    have hB : Y.map (MulAut.conj (t*g)).toMonoidHom ≤ Campbell.F H := by
      rintro z ⟨y,hy,rfl⟩
      exact (Campbell.F_normal).conj_mem y (hF hy) (t*g)
    let : IsElementaryAbelian 2 (Campbell.F H) := omegaOneCenterAmbient_elementaryAbelian _
    exact commutator_eq_bot_iff_le_centralizer.mpr (hA.trans
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hB)))
  · obtain ⟨b,hb,hi⟩ := h.sylow_automorphism_full_actor_conjugates S hB a hV
    let u0 := g⁻¹*t⁻¹*g
    have hu0 : u0 ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hg) (K.inv_mem htK)) hg
    let u : normalizer (W:Set H) := ⟨u0,le_normalizer_conjugateSpanBy Y K hu0⟩
    let X := spanNaturalActor W W' b u
    by_contra hn
    have hYn : ¬Y ≤ centralizer (Y.map (MulAut.conj (u:H)⁻¹).toMonoidHom : Set H) := by
      intro hc
      have hc0 := commutator_eq_bot_iff_le_centralizer.mpr hc
      have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hc0
      rw [map_commutator,conj_map_mul,Subgroup.map_bot] at hm
      have he : g*(u:H)⁻¹=t*g := by change g*(g⁻¹*t⁻¹*g)⁻¹=t*g; group
      rw [he] at hm
      exact hn hm
    have hmove := h.actor_moves_of_conjugates_noncommute S hB a hV b hb u hYn
    have hXS := h.sylow_actor_sup_core S hB a hV hF b hb u hu0 hmove
    have htX : t ∈ X ⊔ pCore 2 H := hXS.symm ▸ ht
    obtain ⟨x,hx,q,hq,htprod⟩ := mem_sup_of_normal_right.mp htX
    have hQN : pCore 2 H ≤ normalizer (A:Set H) := by
      obtain ⟨T,hT,_⟩ := h.sylow
      have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
      have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
      have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans hQS
      have hSN : S ≤ normalizer (Y:Set H) :=
        le_normalizer_automorphismImage S a (Campbell.F H) hFS
          (by let : (Campbell.F H).Normal := Campbell.F_normal; exact le_normalizer_of_normal)
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (hQS.trans hSN)
      rw [map_equiv_normalizer_eq] at hh
      have hQ : (pCore 2 H).map (MulAut.conj g).toMonoidHom=pCore 2 H :=
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
      rwa [hQ] at hh
    have hAq : A.map (MulAut.conj q).toMonoidHom=A := mem_normalizer_iff_map_conj_eq.mp (hQN hq)
    obtain ⟨w,hw,hwx⟩ := hx
    have hcomm := hi u hu0 w hw g hg
    dsimp only at hcomm
    change (w:H)=x at hwx
    rw [hwx] at hcomm
    apply hn
    change ⁅A,Y.map (MulAut.conj (t*g)).toMonoidHom⁆=⊥
    rw [←conj_map_mul Y t g,←htprod,←conj_map_mul A x q,hAq]
    exact hcomm
end CFSG.Quasithin.ChapterC.GlaubermanNiles
