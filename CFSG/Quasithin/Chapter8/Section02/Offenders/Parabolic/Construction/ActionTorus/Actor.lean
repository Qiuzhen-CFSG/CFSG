module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Preparation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Quotient

/-!
# Embedding the E.2 actor in the original group

Source: Aschbacher–Smith, E.2.11(4), E.2.13(2), printed pp.224–225,
and Proposition 8.2.2(7), printed pp.714–715.

The native two-conjugate actor and central intersection inside I map to
exactly V^h ∩ O₂(I) and V ∩ V^h in G. The proved E.2.10 quotient geometry
therefore gives the action-kernel equality. The earlier E.2.11 normalizer
identity transports through the same embedding. The source right
conjugation is represented throughout by conjugation with h⁻¹.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open ChapterE
variable {G : Type*} [Group G]

theorem selected_actor_image [Finite G] (I M V : Subgroup G) (hVI : V ≤ I)
    (S : Sylow 2 I) (i : I)
    (h : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹) :
    (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map I.subtype =
      V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype := by
  rw [h.A_eq_twoCore_inf, map_inf _ _ _ I.subtype_injective]
  rw [TwoConjugate.W, restricted_right_conjugate_image I V hVI i, inf_comm]

theorem selected_intersection_image (I V : Subgroup G) (hVI : V ≤ I) (i : I) :
    (TwoConjugate.Z (V.subgroupOf I) i⁻¹).map I.subtype =
      V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom := by
  rw [TwoConjugate.Z, map_inf _ _ _ I.subtype_injective,
    map_subgroupOf_eq_of_le hVI, TwoConjugate.W, restricted_right_conjugate_image I V hVI i]

theorem selected_actor_kernel [Finite G] (I M V : Subgroup G) (hVI : V ≤ I)
    (S : Sylow 2 I) (i : I)
    (h : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹) :
    (V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) ⊓
      centralizer (V : Set G) = V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom := by
  rw [← selected_actor_image I M V hVI S i h, ← selected_intersection_image I V hVI i,
    ← h.A_inf_centralizer_eq_Z]
  apply le_antisymm
  · rintro x ⟨⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ⟨ha, fun v hv => Subtype.ext (hc v.val hv)⟩, rfl⟩
  · rintro x ⟨a, ⟨ha, hc⟩, rfl⟩
    refine ⟨mem_map_of_mem _ ha, ?_⟩
    intro v hv
    exact congrArg Subtype.val (hc ⟨v, hVI hv⟩ hv)

theorem selected_actor_normalizer [Finite G] (I M V : Subgroup G) (hVI : V ≤ I)
    (S : Sylow 2 I) (i : I)
    (h : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
    (hN : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹ =
      TwoConjugate.W (V.subgroupOf I) i⁻¹ ⊓ normalizer (V.subgroupOf I : Set I)) :
    V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype =
      offenderNormalizer V (i.val)⁻¹ := by
  rw [← selected_actor_image I M V hVI S i h, hN]
  have hn : normalizer (V.subgroupOf I : Set I) =
      (normalizer (V : Set G)).comap I.subtype := by
    exact (comap_normalizer_eq_of_le_range (by simpa using hVI)).symm
  rw [hn, map_inf _ _ _ I.subtype_injective,
    TwoConjugate.W, restricted_right_conjugate_image I V hVI i, map_comap_eq,
    range_subtype]
  have hWI : V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≤ I := by
    rw [← restricted_right_conjugate_image I V hVI i]
    exact map_subtype_le _
  exact le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩)
    (fun x hx => ⟨hx.1, hWI hx.1, hx.2⟩)

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
