module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalGeneration

/-!
# Applying corrected quadratic recognition to the terminal section

The graph intersection argument supplies a fixed-space index at most the
order of the actual nontrivial radius-one actor image. The same actor is
quadratic, and the terminal edge supplies fixed-space generation. Corrected
(5.12) therefore gives an SL₂ isomorphism and natural coordinates on the
literal V_t/Z_t section. Catalogue membership, faithfulness and vanishing
O²-fixed space remain explicit earlier-source module premises.

Source: DGS, *Groups and Graphs* (1985), (7.5), printed p.131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_epsilonTwo_terminal_section_natural
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t a y x : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hva : (graph (family P)).Adj v a) (hua : u ≠ a)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hb : 4 < b (family P))
    (hty : (graph (family P)).Adj t y) (hyx : (graph (family P)).Adj y x)
    (hdx : (graph (family P)).dist v x + 3 = b (family P))
    (hcore : V (family P) v 2 ≤ Q (family P) y)
    [((Q (family P) t).subgroupOf (d t y hty).Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar) W)
    (s : BinaryConjugationSection (d t y hty).Pstar (V (family P) t 1) (Z (family P) t)
      (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf (d t y hty).Pstar))))
    (hesc : ¬ V (family P) a 1 ≤ Q (family P) t)
    (M : BinaryRankOneModel
      ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar))
    (hf : Function.Injective σ)
    (hr : fixedSpace σ (pResidual 2
      ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar)) = ⊥) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      ∃ e : ((d t y hty).Pstar ⧸ (Q (family P) t).subgroupOf (d t y hty).Pstar) ≃* SL(2,k),
        letI : Algebra (ZMod 2) k := ZMod.algebra k 2
        ∃ E : W ≃ₗ[ZMod 2] (Fin 2 → k),
          ∀ g w, E (σ g w) = Matrix.mulVec (e g).val (E w) := by
  let := finite_endpoints h
  let c := d t y hty
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let : Finite (V (family P) t 1) := Finite.of_injective
    (inclusion s.section_le) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun z => (s.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let π := QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)
  let T := c.sylow.mapSurjective (QuotientGroup.mk'_surjective ((Q (family P) t).subgroupOf c.Pstar))
  let A := ((V (family P) a 1).subgroupOf c.Pstar).map π
  have hbnd := graph_epsilonTwo_terminal_section_bound h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hva hua hdu hdt hepsilon hnat₀ hnat₁ hsyl hb hty hyx hdx hcore σ s
  have hAL : V (family P) a 1 ≤ c.Pstar := hbnd.1
  let : Finite (V (family P) a 1) := Finite.of_injective (inclusion hAL) (inclusion_injective _)
  have hE : ((stabilizer (family P) t ⊓ stabilizer (family P) y).pCoreIn 2).subgroupOf
      c.Pstar = c.sylow := by
    rw [←local_sylow_eq_edgeCore c (by rw [hstar]; exact hodd t)
      (source_edge_core_sylow h hB hty)]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  have hAS : A ≤ (T : Subgroup _) := by
    apply map_mono
    rw [←hE]
    exact subgroupOf_mono _ ((graph_V_adjacent_le hva 1).trans
      (hcore.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore h hty.symm)))
  have hvw := (graph_epsilonTwo_even_of_localData h hB L hcov d hstar hodd hdich
    hc hne hvu hepsilon).1
  have htype : v.type = y.type := by
    have he := (same_orbit_iff (family P) v w).mp hvw
    have hw := hwt.1
    have hy := hty.1
    cases hv : v.type <;> cases hw' : w.type <;> cases ht : t.type <;>
      cases hy' : y.type <;> simp_all
  have hgen : GeneratedByFixedSpace σ T := by
    have he := graph_epsilonTwo_radius_section_generated_of_type h hB hvu hty.symm htype
      (d v u hvu) (d u v hvu.symm) c (by rw [hstar]; exact hodd v)
      (by rw [hstar]; exact hodd u) (by rw [hstar]; exact hdich u)
      hepsilon (by rw [hstar]; exact hnat₀) σ s
    rwa [hE] at he
  have hgt : 1 < Nat.card A := by
    rw [actor_image_card_eq_relIndex c.Pstar (Q (family P) t) _ π (QuotientGroup.ker_mk' _) hAL]
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨index_ne_zero_of_finite,fun he => hesc (relIndex_eq_one.mp he)⟩
  have hstrict : Nat.card (W ⧸ fixedSpace σ A) < Nat.card A ^ 2 := by
    have hh : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A := hbnd.2.2
    nlinarith
  obtain ⟨k,_,_,_,n,_,_,e,hn⟩ :=
    (binary_rank_one_bound_and_recognition M σ hf T A hAS hbnd.2.1 hgen hr).2 hstrict
  exact ⟨k,inferInstance,inferInstance,inferInstance,e,hn.2.2.2.2.2.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
