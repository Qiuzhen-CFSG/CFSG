module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneTransport
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceF9
public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure

/-!
# The original A₅ plane-transport input in13.5.13

The original plane and three-space have compatible coordinates, and the
actual residual acts transitively on the nonzero line quotient. Thus the
source13.5.13 deduction now retains only the preceding plane-normalization
statement13.5.11. The index-two seed and the F.9.5(6) centralizer bound
are constructed from the original A₅ context as well.
Source: Aschbacher–Smith13.5.13, printed p.919.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
include d

omit [IsElementaryAbelian 2 V] in
/-- The chosen original module has order sixteen. -/
theorem Context.module_card : Nat.card V = 16 := by
  rw [←d.flag.module.range_eq,←Nat.card_congr (MonoidHom.ofInjective d.flag.module.injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

omit [IsElementaryAbelian 2 V] in
/-- The source seed has index two in its actual chosen module. -/
theorem Context.third_index : V₃.relIndex V = 2 := by
  have hc := (V₃.subgroupOf V).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe d.third_le).toEquiv,d.third_card,d.module_card] at hc
  change 8 * V₃.relIndex V = 16 at hc
  omega

variable
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include hA312 hH hU

/-- Original13.5.13(1), with its module-transport and F.9 inputs discharged.
The displayed remaining antecedent is exactly preceding13.5.11. -/
theorem source13_5_13_of_plane_control
    (hplane : ∀ k ∈ H, V₂ ≤ V ⊓ V.map (MulAut.conj k).toMonoidHom →
      V.map (MulAut.conj k).toMonoidHom ≤ normalizer (V : Set G))
    {g : G} (hg : g ∈ H)
    (hi : V₁ < V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  exact LocalGeometry.twoGroup_join_of_plane_control hf V₂ d.third_index hU
    d.plane_transport hplane hg hi

omit hU hH [IsElementaryAbelian 2 V] in
/-- The other source13.5.13(2) antecedent holds on the actual H-centralizer. -/
theorem source_seed_centralizer_bound : ⁅V,H ⊓ centralizer (V₃ : Set G)⁆ ≤ V₁ := by
  have hc : H ⊓ centralizer (V₃ : Set G) ≤ centralizer (V : Set G) := by
    intro x hx
    exact d.third_centralizer_local.le ⟨d.seed_centralizer hA312 hx.2,hx.2⟩
  rw [commutator_comm]
  have he : ⁅H ⊓ centralizer (V₃ : Set G),V⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hc
  rw [he]
  exact bot_le

end CFSG.Quasithin.Chapter13.Section05.A5Source
