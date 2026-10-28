module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CartanCubicCounts
public import Theory.GroupTheory.CoprimeSubgroupLift

/-!
# The original Cartan embedded in the full orbit automizer

Schur--Zassenhaus splits the already constructed cover on the faithful
whole-span image, whose full kernel is a two-group. Restriction to the
original orbit is faithful on this odd complement: a trivial restriction
fixes the essential seed, whereas the Cartan acts freely on that seed.
Every resulting automizer element retains a representative in the same
original overlap and its prescribed Cartan image. No splitting or
two-group assertion is made for the kernel upstairs in the original H.

Source: Aschbacher--Smith, proof of 3.1.9(6), printed p.578, applied in
8.2.2(1), p.715, refs/quasithin.pdf. The actual M22-code application is
NonFFSourceMathieuShadowRows/M22CodeCartanFieldFour in Chapter12.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD
variable {G D W : Type*} [Group G] [Finite G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {M H V : Subgroup G} {q : H →* D} {ρ : Representation (ZMod 2) D W} {v : W}
  [hU : IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The small natural alternative or the field-four Cartan with its constructed
original cubic chief counts. This names the conclusion at the large essential
quotient boundary; the original source application proves every clause. -/
@[expose] def FieldFourCubicAlternatives [IsElementaryAbelian 2 V]
    (q : H →* D) (ρ : Representation (ZMod 2) D W) (v : W) : Prop :=
  ChapterB.ChiefSmallNaturalAlternatives ρ ∨
    ∃ c : SeedCartan (M := M) q ρ v,
      IsPGroup 3 c.field.Carrierˣ ∧ Nat.card c.field.Carrier = 4 ∧
        CubicOrbitChiefs (V := V) c.originalPreimage q

/-- The same split torus embeds in the full original orbit automizer;
every element retains a lift in the original overlap and its original Cartan image. -/
theorem SeedCartan.exists_orbit_torus
    (c : SeedCartan (M := M) q ρ v)
    (hVH : V ≤ H)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hN : H ⊓ M ≤ normalizer (V : Set G))
    (hc : c.HasSpanCover (normalRepresentation ((conjugateSpan H V).subgroupOf H))) :
    ∃ t : c.field.Carrierˣ →* ChapterE.Automizer V,
      Function.Injective t ∧
      ∀ a, ∃ b : c.originalPreimage,
        q (b : H) = c.embedding a ∧
        ∃ hn : ((b : H) : G) ∈ normalizer (V : Set G),
          V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩ = t a := by
  let τ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
  let P := actionSubgroup τ c.originalPreimage
  obtain ⟨f,hf,he,_,hk⟩ := hc
  have hB : c.originalPreimage.map H.subtype ≤ normalizer (V : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    exact hN hx.1
  obtain ⟨r,hr⟩ := exists_span_orbit_restriction hVH c.originalPreimage hB
  have hker : r.ker ≤ f.ker := by
    intro x hx
    obtain ⟨b,hb,hbx⟩ := x.property
    have hbx' : (⟨actionHom τ b,mem_map_of_mem _ hb⟩ : P) = x := Subtype.ext hbx
    have hz : V.normalizerMonoidHom.rangeRestrict
        ⟨(b : G),hB (mem_map_of_mem _ hb)⟩ = 1 := by
      rw [←hr ⟨b,hb⟩,hbx']
      exact hx
    have hz' : (b : G) ∈ centralizer (V : Set G) := by
      change (⟨(b : G),hB (mem_map_of_mem _ hb)⟩ : normalizer (V : Set G)) ∈
        V.normalizerMonoidHom.rangeRestrict.ker at hz
      rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker] at hz
      exact hz
    apply c.seed_free
    have hc' := he ⟨b,hb⟩
    rw [hbx'] at hc'
    rw [hc']
    exact hv b hz'
  have ho : Odd (Nat.card c.field.Carrierˣ) := by
    rw [Nat.card_units,c.field.card_eq]
    obtain ⟨k,hk⟩ := (by decide : Even 2).pow_of_ne_zero c.field.degree_pos.ne'
    have hp : 0 < 2 ^ c.field.degree := pow_pos (by decide) _
    exact ⟨k-1,by omega⟩
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card (⊤ : Subgroup c.field.Carrierˣ)) := by
    obtain ⟨k,hk⟩ := hk.exists_card_eq
    rw [hk,card_top]
    exact ho.coprime_two_left.pow_left k
  obtain ⟨s,hs⟩ := f.exists_subgroup_section_of_coprime_kernel hf ⊤ hcop
  let j : c.field.Carrierˣ →* P := s.comp (topEquiv.symm.toMonoidHom)
  have hj (a : c.field.Carrierˣ) : f (j a) = a :=
    DFunLike.congr_fun hs (topEquiv.symm a)
  let t := r.comp j
  have ht : Function.Injective t := by
    apply (MonoidHom.ker_eq_bot_iff t).mp
    apply bot_unique
    intro a ha
    have hh : j a ∈ r.ker := ha
    have hh' : f (j a) = 1 := hker hh
    exact mem_bot.mpr ((hj a).symm.trans hh')
  refine ⟨t,ht,?_⟩
  intro a
  obtain ⟨b,hb,hbj⟩ := (j a).property
  have hbj' : (⟨actionHom τ b,mem_map_of_mem _ hb⟩ : P) = j a := Subtype.ext hbj
  refine ⟨⟨b,hb⟩,?_,hB (mem_map_of_mem _ hb),?_⟩
  · have hh := he ⟨b,hb⟩
    rw [hbj',hj] at hh
    exact hh.symm
  · rw [←hr ⟨b,hb⟩,hbj']
    rfl
end CFSG.Quasithin.Chapter8.MathieuShadowRows
