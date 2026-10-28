module

public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import Theory.GroupTheory.SylowNormalIntersection


/-!
# Outer centralizers and Sylow generation in Aut(SL₃(2))

Let I be the actual inner automorphism subgroup. A non-two-group H containing
an ambient Sylow two-subgroup and an outer automorphism contains I. Indeed,
the preimage of H under conjugation contains a Sylow two-subgroup of SL₃(2).
Since the outer quotient is a two-group, this preimage is not a two-group.
If proper, it can be marked as the line parabolic. Every element of H
preserves the preimage, and hence its intrinsic two-residual. The checked
parabolic automorphism calculation then makes every element of H inner,
contradicting the specified outer actor.

Apply this to H = C(z) ∨ P. An actual epimorphism C(z) → S₃ rules out H being
a two-group. This proves the generation input to the binary outer branch
of Aschbacher–Smith E.1.14(1), printed p.214, with the E₁ conventions of
E.1.1–6, printed pp.209–210. The existence of the epimorphism is an explicit
input here and is discharged separately in the source-theorem assembly.
-/

public section

open Subgroup
namespace Matrix.PSL3Two.Automorphisms.OuterCentralizerGeneration

private theorem conj_apply_aut (a : MulAut SL) (g : SL) :
    MulAut.conj (a g) = a * MulAut.conj g * a⁻¹ := by
  ext x
  simp

private theorem inner_preimage_stable (H : Subgroup (MulAut SL))
    (a : MulAut SL) (ha : a ∈ H) :
    (H.comap MulAut.conj).map a.toMonoidHom = H.comap MulAut.conj := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change MulAut.conj (a g) ∈ H
    rw [conj_apply_aut]
    exact H.mul_mem (H.mul_mem ha hg) (H.inv_mem ha)
  · intro hx
    refine ⟨a⁻¹ x, ?_, by simp⟩
    change MulAut.conj (a⁻¹ x) ∈ H
    rw [conj_apply_aut]
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) hx) (H.inv_mem (H.inv_mem ha))

private theorem inner_of_line_preserving (a : MulAut SL)
    (ha : lineParabolicSL.map a.toMonoidHom = lineParabolicSL) :
    a ∈ MulAut.innerSubgroup SL := by
  have hr := map_embedded_pResidual 2 lineParabolicSL a.toMonoidHom
  change (MarkedAutomorphisms.residual lineParabolicSL).map a.toMonoidHom =
    MarkedAutomorphisms.residual (lineParabolicSL.map a.toMonoidHom) at hr
  rw [ha, MarkedAutomorphisms.line_residual] at hr
  obtain ⟨g, _, hg⟩ := MarkedAutomorphisms.line_implementer a (by
    intro x hx
    rw [← hr]
    exact mem_map_of_mem _ hx)
  exact ⟨g, hg.symm⟩

private theorem isTwoGroup_of_inner_preimage (H : Subgroup (MulAut SL))
    (hK : IsPGroup 2 (H.comap MulAut.conj)) : IsPGroup 2 H := by
  intro a
  obtain ⟨n, hn⟩ := outer_sl_isTwoGroup
    (QuotientGroup.mk' (MulAut.innerSubgroup SL) a.val)
  have hi : a.val ^ (2 ^ n) ∈ MulAut.innerSubgroup SL := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (MulAut.innerSubgroup SL) (a.val ^ (2 ^ n)) = 1
    rw [map_pow]
    exact hn
  obtain ⟨g, hg⟩ := hi
  have hgK : g ∈ H.comap MulAut.conj := by
    change MulAut.conj g ∈ H
    rw [hg]
    exact H.pow_mem a.property _
  obtain ⟨m, hm⟩ := hK ⟨g, hgK⟩
  have hm' : g ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  refine ⟨n + m, Subtype.ext ?_⟩
  change a.val ^ (2 ^ (n + m)) = 1
  rw [pow_add, pow_mul, ← hg, ← map_pow, hm', map_one]

private theorem exists_inner_sylow (P : Sylow 2 (MulAut SL)) :
    ∃ S : Sylow 2 SL, ∀ g ∈ S, MulAut.conj g ∈ P := by
  let i : SL ≃* MulAut.innerSubgroup SL :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_eq_bot)
  obtain ⟨S₀, hS₀⟩ := P.exists_subgroupOf_eq_of_normal (MulAut.innerSubgroup SL)
  refine ⟨S₀.mapSurjective (f := i.symm.toMonoidHom) i.symm.surjective, ?_⟩
  rintro g ⟨a, ha, rfl⟩
  have hp : a.val ∈ P := by
    change a ∈ (P : Subgroup (MulAut SL)).subgroupOf (MulAut.innerSubgroup SL)
    rwa [← hS₀]
  have hi : MulAut.conj (i.symm a) = a.val :=
    congrArg Subtype.val (i.apply_symm_apply a)
  change MulAut.conj (i.symm a) ∈ P
  rwa [hi]

/-- A non-two-group containing a full Sylow two-subgroup and an outer actor
contains the inner automorphism subgroup. -/
theorem inner_le_of_sylow_le_of_not_isTwoGroup
    (P : Sylow 2 (MulAut SL)) (H : Subgroup (MulAut SL))
    (hPH : (P : Subgroup (MulAut SL)) ≤ H) (hH : ¬ IsPGroup 2 H)
    (a : MulAut SL) (ha : a ∈ H) (haouter : a ∉ MulAut.innerSubgroup SL) :
    MulAut.innerSubgroup SL ≤ H := by
  by_contra hIH
  let K : Subgroup SL := H.comap MulAut.conj
  have hK : K ≠ ⊤ := by
    intro htop
    apply hIH
    rintro b ⟨g, rfl⟩
    exact (show g ∈ K from htop ▸ mem_top g)
  have hKtwo : ¬ IsPGroup 2 K := fun h => hH (isTwoGroup_of_inner_preimage H h)
  obtain ⟨S, hS⟩ := exists_inner_sylow P
  have hSK : (S : Subgroup SL) ≤ K := fun g hg => hPH (hS g hg)
  obtain ⟨e, _, he⟩ := exists_sylow_line_marking equiv S K hSK hK hKtwo
  have hstable : K.map a.toMonoidHom = K := inner_preimage_stable H a ha
  let b := MulAut.congr e a
  have hb : lineParabolicSL.map b.toMonoidHom = lineParabolicSL := by
    rw [← he, Subgroup.map_map]
    have heq : b.toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by
      ext x
      simp [b, MulAut.congr_apply]
    rw [heq, ← Subgroup.map_map, hstable]
  obtain ⟨g, hg⟩ := inner_of_line_preserving b hb
  obtain ⟨x, hx⟩ := (MulAut.congr_inner_iff e a).mp ⟨g, hg.symm⟩
  exact haouter ⟨x, hx.symm⟩

private theorem not_two_perm_three : ¬ IsPGroup 2 (Equiv.Perm (Fin 3)) := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hd : 3 ∣ 2 ^ n := by rw [← hn, hc]; decide
  have := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
  norm_num at this

/-- The S₃ epimorphism excludes a two-group centralizer, forcing generation
with every Sylow two-subgroup containing the outer involution. -/
theorem inner_le_centralizer_sup_sylow
    (P : Sylow 2 (MulAut SL)) (z : MulAut SL)
    (hzP : z ∈ P) (_hz2 : z ^ 2 = 1) (hzouter : z ∉ MulAut.innerSubgroup SL)
    (π : centralizer ({z} : Set (MulAut SL)) →* Equiv.Perm (Fin 3))
    (hπ : Function.Surjective π) :
    MulAut.innerSubgroup SL ≤ centralizer ({z} : Set (MulAut SL)) ⊔
      (P : Subgroup (MulAut SL)) := by
  apply inner_le_of_sylow_le_of_not_isTwoGroup P _ le_sup_right _ z
    (show z ∈ centralizer ({z} : Set (MulAut SL)) ⊔ (P : Subgroup (MulAut SL)) from
      (show (P : Subgroup (MulAut SL)) ≤ _ from le_sup_right) hzP) hzouter
  intro h
  exact not_two_perm_three ((h.to_le le_sup_left).of_surjective π hπ)

end Matrix.PSL3Two.Automorphisms.OuterCentralizerGeneration
