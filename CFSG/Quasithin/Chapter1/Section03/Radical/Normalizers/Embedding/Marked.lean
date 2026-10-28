module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Local

/-!
# Marked subgroups in the containing-component quotient

The A.3.12 list lives in N/O₂(N), whereas the parabolic argument uses
K/O₂(K). The equivalence below is induced by inclusion of the actual
C-component K in N, and its formula on representatives retains every
embedded subgroup. In particular the chosen odd subgroup P is not replaced
by an unspecified elementary subgroup after identifying the ambient model.

`MarkedFiveExtension` specifies the input needed by the independent
PSL₃(5) parabolic-recognition argument. It asserts an extension with its
marked kernel and imposes no splitting.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.513.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The marked kernel, its elementary coordinates, and the exact quotient.
This is a target for the reduction, not an assumed source theorem. -/
def MarkedFiveExtension (B P : Subgroup G) : Prop :=
  P ≤ B ∧ Section02.LocalModels.ElementaryModel 5 2 P ∧
    ∃ _ : (P.subgroupOf B).Normal,
      Nonempty ((B ⧸ P.subgroupOf B) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

/-- The isomorphism to the component image is induced by the actual inclusion. -/
def componentQuotientEquiv {K N : Subgroup G} (hKN : K ≤ N)
    (hK : (K.subgroupOf N).IsCComponent) :
    XiQuotient K ≃* (K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKN).symm
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKN).symm)).trans
    (cComponentTwoCoreQuotientEquiv hK)

/-- The representative formula fixes the marking of every subgroup of K. -/
theorem componentQuotientEquiv_apply_mk {K N : Subgroup G} (hKN : K ≤ N)
    (hK : (K.subgroupOf N).IsCComponent) (k : K) :
    ((componentQuotientEquiv hKN hK (QuotientGroup.mk' (pCore 2 K) k)) :
      XiQuotient N) = QuotientGroup.mk' (pCore 2 N) ⟨k, hKN k.property⟩ := by
  rfl

/-- Compatibility for arbitrary marked D ≤ K, including the actual P and Y.
The right side is the image in the very quotient used by A.3.12. -/
theorem componentQuotientEquiv_map_subgroup {D K N : Subgroup G}
    (hDK : D ≤ K) (hKN : K ≤ N) (hK : (K.subgroupOf N).IsCComponent) :
    (((D.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
      (componentQuotientEquiv hKN hK).toMonoidHom).map
        ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))).subtype =
      (D.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) := by
  ext x
  constructor
  · rintro ⟨a, ⟨b, ⟨d, hd, rfl⟩, rfl⟩, rfl⟩
    exact ⟨⟨d, hKN d.property⟩, hd, componentQuotientEquiv_apply_mk hKN hK d |>.symm⟩
  · rintro ⟨d, hd, rfl⟩
    let k : K := ⟨d, hDK hd⟩
    refine ⟨componentQuotientEquiv hKN hK (QuotientGroup.mk' (pCore 2 K) k),
      ⟨QuotientGroup.mk' (pCore 2 K) k, ⟨k, hd, rfl⟩, rfl⟩, ?_⟩
    exact componentQuotientEquiv_apply_mk hKN hK k

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
