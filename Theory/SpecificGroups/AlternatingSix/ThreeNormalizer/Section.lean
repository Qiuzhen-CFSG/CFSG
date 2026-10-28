module

public import Theory.SpecificGroups.AlternatingSix.ThreeNormalizer

/-!
# An A₆ section obstructs an exponent-two Sylow-nine action

A Sylow three of a subgroup mapping onto A₆ maps to a Sylow nine. If the
ambient Sylow three also has order nine, the inclusion is therefore a full
Sylow inclusion. The actual A₆ normalizer actor then contradicts an action
in which every normalizer square centralizes that Sylow subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.7, p.245.
-/

public section
open Subgroup
namespace AlternatingSix.ThreeNormalizer
variable {G : Type*} [Group G] [Finite G]
theorem no_section_of_sylow_nine_square_centralizers
    (P:Sylow 3 G) (hP:Nat.card P=9)
    (hN:∀g∈normalizer (P:Set G),g^2∈centralizer (P:Set G))
    (M:Subgroup G) (f:M→*A6) (hf:Function.Surjective f) : False := by
  let Q : Sylow 3 M := Classical.choice inferInstance
  let Y := (Q:Subgroup M).map M.subtype
  have hYp : IsPGroup 3 Y := Q.isPGroup'.map M.subtype
  obtain ⟨T,hYT⟩ := hYp.exists_le_sylow
  have hT9 : Nat.card T=9 := by rw [T.card_eq_multiplicity,←P.card_eq_multiplicity,hP]
  have hY9 : 9≤Nat.card Y := by
    have hQ9 : Nat.card ((Q:Subgroup M).map f)=9 := by
      change Nat.card (Q.mapSurjective hf)=9
      have hc : Nat.card A6=360 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      rw [Sylow.card_eq_multiplicity,hc]
      decide +kernel
    rw [card_map_of_injective M.subtype_injective,←hQ9]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ f)
  have hTY : (T:Subgroup G)=Y := (eq_of_le_of_card_ge hYT (hT9 ▸ hY9)).symm
  obtain ⟨g,hg,hgc⟩ := exists_square_noncentral_of_surjective f hf Q
  have hgY : (g:G)∈normalizer (Y:Set G) :=
    (Q:Subgroup M).le_normalizer_map M.subtype (mem_map_of_mem M.subtype hg)
  have hgcY : (g:G)^2∉centralizer (Y:Set G) := by
    intro hh
    apply hgc
    intro q hq
    apply Subtype.ext
    exact hh q (mem_map_of_mem M.subtype hq)
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq G T P
  have he : Y.map (MulAut.conj k).toMonoidHom=(P:Subgroup G) := by
    rw [←hTY]
    exact congrArg Sylow.toSubgroup hk
  have hgn : k*(g:G)*k⁻¹∈normalizer ((P:Subgroup G):Set G) := by
    rw [←he,←map_equiv_normalizer_eq Y (MulAut.conj k)]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hgY
  have hfix := hN _ hgn
  apply hgcY
  intro x hx
  have hxx : k*x*k⁻¹∈(P:Subgroup G) := he ▸ mem_map_of_mem (MulAut.conj k).toMonoidHom hx
  have hh := hfix (k*x*k⁻¹) hxx
  apply (MulAut.conj k).injective
  rw [map_mul,map_mul,map_pow]
  exact hh
end AlternatingSix.ThreeNormalizer
