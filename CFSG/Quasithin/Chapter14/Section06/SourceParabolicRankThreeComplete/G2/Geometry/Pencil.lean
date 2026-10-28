module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Flag
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.Points
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The pencil bound for a moved G₂ flag

A point-fixing conjugation which is an actual octonion-model operator preserves
the pencil through that point. Its lines span dimension three in both the
natural six-space and the Weyl seven-space. Thus a moving line of order four
has conjugate span of order eight. The action and geometric marking premises
are explicit here; the block-coordinate calculation discharges them.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
The concrete pencil calculation uses the attributed ATLAS models, LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
open Atlas.G2 Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Chapter14.Section07.G2Exclusion.MarkedGeometry
open Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

def spaceImage (i : Multiplicative W →* G) (P : Submodule (ZMod 2) W) : Subgroup G :=
  P.toAddSubgroup.toSubgroup.map i

/-- The original point fixer acts inside the three-dimensional pencil. -/
theorem conjugateSpan_le_pencil
    (f : SingularMap W) (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant ρ) (i : Multiplicative W →* G) (hi : Function.Injective i)
    (V Z J : Subgroup G) (L : ZeroProductLine (ZMod 2)) (p : SingularPoints (ZMod 2))
    (hV : V = spaceImage i (f.line L)) (hZ : Z = spaceImage i (f.point p))
    (hp : pointOnLine p L) (hfix : J ≤ centralizer (Z : Set G))
    (hact : ∀ j ∈ J, ∃ g : Model (ZMod 2), ∀ w : W,
      i (Multiplicative.ofAdd (ρ g w)) = j * i (Multiplicative.ofAdd w) * j⁻¹) :
    conjugateSpanBy V J ≤ spaceImage i (pencilSpan f p) := by
  apply (closure_le _).mpr
  rintro _ ⟨j,hj,v,hv,rfl⟩
  obtain ⟨g,hg⟩ := hact j hj
  have hpoint (w : W) (hw : w ∈ f.point p) : ρ g w = w := by
    apply Multiplicative.ofAdd.injective
    apply hi
    rw [hg]
    have hz : i (Multiplicative.ofAdd w) ∈ Z := hZ ▸ mem_map_of_mem i hw
    rw [← mem_centralizer_iff.mp (hfix hj) _ hz, mul_inv_cancel_right]
  have hgp : g • p = p := by
    apply f.point_injective
    rw [f.point_equivariant ρ hf]
    apply le_antisymm
    · rintro _ ⟨w,hw,rfl⟩
      rwa [hpoint w hw]
    · intro w hw
      exact ⟨w,hw,hpoint w hw⟩
  rw [hV] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  change j * i (Multiplicative.ofAdd w.toAdd) * j⁻¹ ∈ _
  rw [← hg w.toAdd]
  apply mem_map_of_mem
  have hwP : w.toAdd ∈ pencilSpan f p :=
    (le_iSup (fun L : {L : ZeroProductLine (ZMod 2) // pointOnLine p L} =>
      f.line L.val) ⟨L,hp⟩) hw
  have hh := Submodule.mem_map_of_mem (f := ρ g) hwP
  rwa [pencilSpan_equivariant f ρ hf, hgp] at hh

/-- Movement forces strict growth from four to eight inside the pencil. -/
theorem conjugateSpan_card_of_pencil [Finite G]
    (f : SingularMap W) (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant ρ) (i : Multiplicative W →* G) (hi : Function.Injective i)
    (V J : Subgroup G) (p : SingularPoints (ZMod 2))
    (hcard : Nat.card V = 4) (hmove : ¬ J ≤ normalizer (V : Set G))
    (hle : conjugateSpanBy V J ≤ spaceImage i (pencilSpan f p)) :
    Nat.card (conjugateSpanBy V J) = 8 := by
  have hP : Nat.card (spaceImage i (pencilSpan f p)) = 8 := by
    rw [spaceImage, Subgroup.card_map_of_injective hi]
    change Nat.card (pencilSpan f p) = 8
    let : Module.Finite (ZMod 2) (pencilSpan f p) :=
      Module.finite_of_finrank_eq_succ (pencilSpan_finrank f ρ hf p)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), pencilSpan_finrank f ρ hf p]
    norm_num
  have hlt : 4 < Nat.card (conjugateSpanBy V J) := by
    have hn : V ≠ conjugateSpanBy V J := by
      intro he
      exact hmove (he ▸ le_normalizer_conjugateSpanBy V J)
    by_contra! hh
    exact hn (Subgroup.eq_of_le_of_card_ge (le_conjugateSpanBy V J) (by omega))
  have hd : Nat.card (conjugateSpanBy V J) ∣ 8 := hP ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨n,hn⟩ := hd
  have hn0 : 0 < n := by by_contra! hh; simp [show n = 0 by omega] at hn
  have hn1 : n = 1 := by nlinarith
  simpa only [hn1, mul_one] using hn.symm

end CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
