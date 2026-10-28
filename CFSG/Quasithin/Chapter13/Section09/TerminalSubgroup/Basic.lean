module

public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import Theory.GroupTheory.PResidual.CentralSylowCharacter
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The literal terminal residual in 13.9.1

The terminal group is O²(C_G(E)), embedded in the original ambient group.
Subgroup inclusions carry the two local residuals into this group. Transfer
to the E-coordinate of a marked Sylow product E × T₂ proves E ∩ H = 1.
In particular, E is never assumed to be a subgroup of H.

The Sylow product and the local centralization assertions are earlier local
geometry inputs; the subsequent dihedral recognition and automorphism
arguments are separate. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, proof of 13.9.1, printed pp.973–974 (PDF pp.990–991).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup

open Subgroup

variable {G : Type*} [Group G]

/-- The intrinsic two-residual, embedded by the original subgroup inclusion. -/
abbrev residual (U : Subgroup G) : Subgroup G := (pResidual 2 U).map U.subtype

/-- The source's H, without a replacement by an abstract recognized model. -/
abbrev terminal (E : Subgroup G) : Subgroup G := residual (centralizer (E : Set G))

theorem residual_le (U : Subgroup G) : residual U ≤ U := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- Both local residuals enter H through the literal inclusion in C_G(E). -/
theorem residual_le_terminal (E U : Subgroup G)
    (hU : U ≤ centralizer (E : Set G)) : residual U ≤ terminal E := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨Subgroup.inclusion hU y, ?_, rfl⟩
  exact map_pResidual_le 2 (Subgroup.inclusion hU) (mem_map_of_mem _ hy)

/-- The second local residual enters H even when only that residual, rather
than its whole overgroup C_K(t), centralizes E (13.9.10). -/
theorem residual_le_terminal_of_residual_centralizes [Finite G]
    (E U : Subgroup G) (hU : residual U ≤ centralizer (E : Set G)) :
    residual U ≤ terminal E := by
  have h := residual_le_terminal E (residual U) hU
  have he : residual (residual U) = residual U := by
    unfold residual
    rw [(pResidual_eq_top_iff 2 _).mpr (isPPerfect_embedded_pResidual 2 U)]
    exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)
  rwa [he] at h

/-- E centralizes H; this does not assert E ≤ H. -/
theorem centralizes_terminal (E : Subgroup G) : E ≤ centralizer (terminal E : Set G) :=
  le_centralizer_iff.mpr (residual_le _)

/-- Normalizing E normalizes its centralizer's characteristic two-residual. -/
theorem normalizer_le_terminal_normalizer (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer (terminal E : Set G) := by
  have hle := centralizer_le_normalizer (E : Set G)
  exact (normal_subgroupOf_iff_le_normalizer ((residual_le _).trans hle)).mp
    (normal_embedded_pResidual_subgroupOf 2 hle inferInstance)

/-- The source's M₁ normalizes H through E = O₂(M₁). -/
theorem normalizes_terminal_of_core (E M₁ : Subgroup G) (hE : E = M₁.pCoreIn 2) :
    M₁ ≤ normalizer (terminal E : Set G) := by
  apply le_trans ?_ (normalizer_le_terminal_normalizer E)
  rw [hE]
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 M₁).le_normalizer_map M₁.subtype

/-- An element of E which belongs to C_G(E) is central in that centralizer. -/
theorem mem_center_centralizer (E : Subgroup G) (x : centralizer (E : Set G))
    (hx : (x : G) ∈ E) : x ∈ center (centralizer (E : Set G)) := by
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact (mem_centralizer_iff.mp y.property x hx).symm

/-- Transfer removes the central E-coordinate from the actual residual H.
The equivalence is marked by multiplication in G, not just by group order. -/
theorem disjoint_terminal_of_sylow_product [Finite G]
    (E D : Subgroup G) [IsMulCommutative E] (hE : IsPGroup 2 E)
    (S : Sylow 2 (centralizer (E : Set G)))
    (e : E × D ≃* S)
    (he : ∀ a b, (((e (a, b) : S) : centralizer (E : Set G)) : G) =
      (a : G) * (b : G)) : Disjoint E (terminal E) := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  apply disjoint_def.mpr
  intro x hx hH
  obtain ⟨y, hy, hyx⟩ := hH
  let a : E := ⟨x, hx⟩
  let s : S := e (a, 1)
  have hs : (((s : S) : centralizer (E : Set G)) : G) = x := by
    simpa only [Subgroup.coe_one, mul_one] using he a 1
  have hsy : (s : centralizer (E : Set G)) = y := Subtype.ext (hs.trans hyx.symm)
  let f : S →* E := (MonoidHom.fst E D).comp e.symm.toMonoidHom
  have hf := S.character_eq_one_of_central_mem_pResidual f hE s
    (mem_center_centralizer E _ (hs.symm ▸ hx)) (hsy.symm ▸ hy)
  have ha : a = 1 := by simpa [f, s] using hf
  exact congrArg Subtype.val ha

end CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup
