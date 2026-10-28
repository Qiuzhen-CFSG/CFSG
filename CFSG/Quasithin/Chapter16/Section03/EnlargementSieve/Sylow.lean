module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The two Sylow centralizers in 16.3.11

Apply 16.3.8 uniformly to contrary involutions in the fixed T_C. Conjugacy
inside C_G(L) preserves that contrary property. Their centralizers in T_C
all have order four, so the fully centralized Sylow criterion proves
⟨z,t⟩ is Sylow in C_G(t) ∩ C_G(L).

Any element centralizing L fixes the component K containing L: otherwise
the distinct components would commute and force L to be abelian. Thus
C_G(t) ∩ C_G(K) is normal in C_G(t) ∩ C_G(L). Restriction of the first
Sylow subgroup gives ⟨t⟩, since z does not centralize K.

This proves the first two conclusions of Aschbacher–Smith, 16.3.11,
printed p.1181, conditionally on the full earlier 16.3.8 statement and
16.1.7's proper component/commutator branch. The universal shape premise
is exactly the earlier assertion applied to each contrary involution;
its discharge remains with the §16.3 assembly owner.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.EnlargementSieve
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

private theorem conjugate_counterexample (h : TerminalCounterexample T z L t)
    (g : G) (hg : g ∈ centralizer (L : Set G))
    (hm : (MulAut.conj g) t ∈ commutingSylow T L) :
    TerminalCounterexample T z L ((MulAut.conj g) t) := by
  let e := MulAut.conj g
  refine ⟨h.localSetup, h.normal, (e.orderOf_eq t).trans h.involution, hm, ?_⟩
  intro hc
  have he : e.symm.toMonoidHom = (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    apply e.injective
    simp [e, MulAut.conj_apply, mul_assoc]
  have hback : L.map e.symm.toMonoidHom = L := by
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (L : Set G)).inv_mem (centralizer_le_normalizer _ hg))
  have hmap := (show Theory.GroupTheory.IsComponentIn L
    (involutionCentralizer (e t)) from hc).map e.symm
  rw [hback, involutionCentralizer, map_centralizer_equiv,
    Set.image_singleton, e.symm_apply_apply] at hmap
  exact h.not_component hmap

/-- Uniform 16.3.8 gives the first Sylow conclusion of 16.3.11. -/
theorem first_sylow_of_uniform_shape [Finite G]
    (h : TerminalCounterexample T z L t)
    (hshape : ∀ a : G, TerminalCounterexample T z L a →
      NonterminalCentralizerShape T z L a) :
    ∃ P : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (L : Set G)),
      (P : Subgroup ↥(involutionCentralizer t ⊓ centralizer (L : Set G))).map
        (involutionCentralizer t ⊓ centralizer (L : Set G)).subtype =
          zpowers z ⊔ zpowers t := by
  let C := centralizer (L : Set G)
  obtain ⟨S, hS⟩ := h.localSetup.exists_commutingSylow_of_normal h.normal
  have hSmap : (S : Subgroup C).map C.subtype = commutingSylow T L := by
    rw [hS, subgroupOf_map_subtype]
    rfl
  let f : S →* G := C.subtype.comp (S : Subgroup C).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hmap (y : S) : (centralizer ({y} : Set S)).map f =
      commutingSylow T L ⊓ involutionCentralizer (f y) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨hSmap ▸ mem_map_of_mem C.subtype b.property, ?_⟩
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hb)
    · intro ha
      have haS : a ∈ (S : Subgroup C).map C.subtype := hSmap.symm ▸ ha.1
      obtain ⟨b, hb, rfl⟩ := haS
      refine ⟨⟨b, hb⟩, ?_, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply hf
      simpa only [map_mul, f, MonoidHom.comp_apply, Subgroup.coe_subtype] using
        mem_centralizer_singleton_iff.mp ha.2
  let xC : C := ⟨t, h.mem_commutingSylow.2⟩
  have hxS : xC ∈ (S : Subgroup C) := by rw [hS]; exact h.mem_commutingSylow.1
  let x : S := ⟨xC, hxS⟩
  have hcard (y : S) : Nat.card (centralizer ({y} : Set S)) =
      Nat.card (commutingSylow T L ⊓ involutionCentralizer (f y) : Subgroup G) := by
    rw [← hmap y, card_map_of_injective hf]
  have hbound (y : S) (hy : IsConj (x : C) (y : C)) :
      Nat.card (centralizer ({y} : Set S)) ≤ Nat.card (centralizer ({x} : Set S)) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hy
    have he : (MulAut.conj (g : G)) t = f y := congrArg Subtype.val hg
    have hm : f y ∈ commutingSylow T L := hSmap ▸ mem_map_of_mem C.subtype y.property
    have hc : TerminalCounterexample T z L (f y) :=
      he ▸ conjugate_counterexample h g g.property (he.symm ▸ hm)
    rw [hcard y, hcard x, show f x = t from rfl, (hshape (f y) hc).centralizer_eq,
      (hshape t h).centralizer_eq, (four_group hc).2, (four_group h).2]
  obtain ⟨R, hR⟩ := S.exists_centralizer_sylow_of_card_bound x hbound
  let H := involutionCentralizer t ⊓ C
  let H₀ := centralizer ({xC} : Set C)
  let e : H₀ ≃* H :=
    { toFun := fun a => ⟨a.1, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.2)), a.1.2⟩
      invFun := fun a => ⟨⟨a, a.2.2⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp a.2.1))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((R : Subgroup H₀).map e.toMonoidHom).map H.subtype = _
  rw [map_map]
  have he : H.subtype.comp e.toMonoidHom = C.subtype.comp H₀.subtype := rfl
  rw [he, ← map_map, hR, map_map]
  exact (hmap x).trans (hshape t h).centralizer_eq


variable {K : Subgroup G}

/-- Centralizing the nonabelian seed fixes the component containing it. -/
theorem seed_centralizer_normalizes (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t K) (hLK : L ≤ K) :
    involutionCentralizer t ⊓ centralizer (L : Set G) ≤ normalizer K := by
  intro g hg
  have hLc : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ hg.2)
  have hKc := ComponentTransfer.IsComponentIn.conjugate hK hg.1
  have hLcK : L ≤ K.conjBy g := by
    rw [← hLc]
    exact map_mono hLK
  have he : K.map (MulAut.conj g).toMonoidHom = K := by
    by_contra hn
    have hc := ComponentTransfer.IsComponentIn.commute_of_ne hK hKc (Ne.symm hn)
    have hLcomm : ⁅L, L⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hLK hLcK).trans hc.le)
    let := h.localSetup.component.quasisimple
    rw [commutator_eq_self] at hLcomm
    exact (show Theory.GroupTheory.IsComponentIn L (involutionCentralizer z) from
      h.localSetup.component).ne_bot hLcomm
  exact mem_normalizer_iff_map_conj_eq.mpr he

/-- The actual component centralizer is normal in the seed centralizer. -/
theorem larger_centralizer_normal (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t K) (hLK : L ≤ K) :
    ((involutionCentralizer t ⊓ centralizer (K : Set G)).subgroupOf
      (involutionCentralizer t ⊓ centralizer (L : Set G))).Normal := by
  let H := involutionCentralizer t ⊓ centralizer (L : Set G)
  let N := involutionCentralizer t ⊓ centralizer (K : Set G)
  let f : H →* normalizer K := inclusion (seed_centralizer_normalizes h hK hLK)
  have he : N.subgroupOf H = ((centralizer (K : Set G)).subgroupOf (normalizer K)).comap f := by
    ext x
    exact and_iff_right x.property.1
  rw [he]
  infer_instance

/-- A proper subgroup of the elementary four containing t, but omitting z,
is exactly ⟨t⟩. -/
private theorem four_inf_eq (h : TerminalCounterexample T z L t) [Finite G]
    (N : Subgroup G) (htN : t ∈ N) (hzN : z ∉ N) :
    (zpowers z ⊔ zpowers t) ⊓ N = zpowers t := by
  let E := zpowers z ⊔ zpowers t
  have hEcard : Nat.card E = 4 := (four_group h).2
  have htE : zpowers t ≤ E ⊓ N := le_inf le_sup_right (zpowers_le.mpr htN)
  have hd : Nat.card (E ⊓ N : Subgroup G) ∣ 4 := by
    simpa only [hEcard] using (card_dvd_of_le (inf_le_left : E ⊓ N ≤ E))
  have hlo : 2 ≤ Nat.card (E ⊓ N : Subgroup G) := by
    simpa only [Nat.card_zpowers, h.involution] using card_le_of_le htE
  have hhi : Nat.card (E ⊓ N : Subgroup G) < 4 := by
    by_contra hn
    have he : E ⊓ N = E := eq_of_le_of_card_ge inf_le_left
      (hEcard ▸ (by omega))
    exact hzN ((he.symm ▸ (show z ∈ E from (le_sup_left : zpowers z ≤ E) (mem_zpowers z))).2)
  have hc : Nat.card (E ⊓ N : Subgroup G) = 2 := by
    interval_cases hn : Nat.card (E ⊓ N : Subgroup G)
    · rfl
    · norm_num at hd
  exact (eq_of_le_of_card_ge htE (by rw [hc, Nat.card_zpowers, h.involution])).symm

/-- The second Sylow conclusion follows by normal restriction from the first. -/
theorem second_sylow_of_first [Finite G] (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    (P : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (L : Set G)))
    (hP : (P : Subgroup ↥(involutionCentralizer t ⊓ centralizer (L : Set G))).map
      (involutionCentralizer t ⊓ centralizer (L : Set G)).subtype = zpowers z ⊔ zpowers t) :
    ∃ Q : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)),
      (Q : Subgroup ↥(involutionCentralizer t ⊓ centralizer (enlargement t L : Set G))).map
        (involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)).subtype = zpowers t := by
  let K := enlargement t L
  let H := involutionCentralizer t ⊓ centralizer (L : Set G)
  let N := involutionCentralizer t ⊓ centralizer (K : Set G)
  have hLK : L ≤ K := ComponentTransfer.le_layerClosure _ _
  have hNH : N ≤ H := inf_le_inf_left _ (centralizer_le hLK)
  let : (N.subgroupOf H).Normal := larger_centralizer_normal h hK hLK
  obtain ⟨Q, hQ⟩ := ComponentTransfer.exists_restricted_sylow hNH
    (inferInstance : (N.subgroupOf H).Normal).isSubnormal P
  refine ⟨Q, ?_⟩
  rw [hQ, hP]
  apply four_inf_eq h N
  · refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    exact fun k hk => mem_centralizer_singleton_iff.mp (enlargement_le h hk)
  · intro hz
    have hb : ⁅zpowers z, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (zpowers_le.mpr hz.2)
    rw [commutator_comm, hcomm] at hb
    exact (show Theory.GroupTheory.IsComponentIn K (involutionCentralizer t) from hK).ne_bot hb


/-- Both source Sylow conclusions for the actual enlargement, before the
remaining model and lift exclusions in 16.3.11(3). -/
theorem both_sylow_centralizers [Finite G] (h : TerminalCounterexample T z L t)
    (hshape : ∀ a : G, TerminalCounterexample T z L a →
      NonterminalCentralizerShape T z L a)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L) :
    (∃ P : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (L : Set G)),
      (P : Subgroup ↥(involutionCentralizer t ⊓ centralizer (L : Set G))).map
        (involutionCentralizer t ⊓ centralizer (L : Set G)).subtype =
          zpowers z ⊔ zpowers t) ∧
    (∃ Q : Sylow 2 ↥(involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)),
      (Q : Subgroup ↥(involutionCentralizer t ⊓ centralizer (enlargement t L : Set G))).map
        (involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)).subtype = zpowers t) := by
  obtain ⟨P, hP⟩ := first_sylow_of_uniform_shape h hshape
  exact ⟨⟨P, hP⟩, second_sylow_of_first h hK hcomm P hP⟩

end CFSG.Quasithin.Chapter16.EnlargementSieve
