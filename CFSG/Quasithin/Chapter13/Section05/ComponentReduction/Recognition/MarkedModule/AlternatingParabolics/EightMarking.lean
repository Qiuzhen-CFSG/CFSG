module
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.Eight
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Actors

/-!
# The original A₈ pair marking and tilde generation

The original star image of V has order two and is centralized by L₁*T*.
In the A₈ branch, component normality and simplicity put V* inside K*.
Its intersection with the full Sylow T* is therefore a Sylow of A₈.
The marked local residual is nontrivial and two-perfect, so the local
intersection properly contains this Sylow. The concrete actor-centralizer
calculation identifies it with an even pair stabilizer.

The established augmentation-cover generation then gives the literal
Ũ_H=[Ũ_H,L̃₁]. The full T* is retained throughout, including any elements
outside K*V*. Natural coordinates remain on the central quotient of the
original module; no splitting of that module is assumed.

Source: Aschbacher–Smith 13.5.21(5–6), printed p.924, supplying the original
commutator hypothesis of 13.5.14, printed p.919.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
open Section08.Source
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) {K : Subgroup G}

include h in
/-- The original order-two actor marks the literal local intersection. -/
theorem alternating_eight_pair_marking
    (s : Selected D K)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      alternatingGroup (Fin 8)) :
    ∃ g : alternatingGroup (Fin 8),
      ((localStar D).subgroupOf (starImage D.H K ⊔ starImage D.H D.V)).map
        e.toMonoidHom = (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map
          (MulAut.conj g).toMonoidHom := by
  let B := starImage D.H K ⊔ starImage D.H D.V
  have hBK : B = starImage D.H K := alternating_eight_actor_eq_component D h s hSQ hLK hm e
  have hn := normal_in_H s h hSQ hLK hm
  let : (starImage D.H K).Normal := hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  let : B.Normal := hBK ▸ inferInstance
  obtain ⟨R, hR⟩ := (starSylow D h).exists_subgroupOf_eq_of_normal B
  let S := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let J := ((localStar D).subgroupOf B).map e.toMonoidHom
  have hSJ : (S : Subgroup (alternatingGroup (Fin 8))) ≤ J := by
    change (R : Subgroup B).map e.toMonoidHom ≤ J
    exact map_mono (hR ▸ comap_mono (show starImage D.H D.T ≤ localStar D from le_sup_right))
  have hLB : starImage D.H D.L₁ ≤ B := (map_mono (comap_mono hLK)).trans le_sup_left
  have hne : J ≠ (S : Subgroup (alternatingGroup (Fin 8))) := by
    intro he
    have he' : (localStar D).subgroupOf B = (R : Subgroup B) :=
      map_injective e.injective he
    rw [hR] at he'
    apply localStar_not_le_sylow D h hm
    apply sup_le _ le_rfl
    intro x hx
    have hh : (⟨x, hLB hx⟩ : B) ∈ (localStar D).subgroupOf B := mem_sup_left hx
    rw [he'] at hh
    exact hh
  have hvcard := LocalGeometry.star_V_card_two h hindex hU
  have hvbot : starImage D.H D.V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hvcard
    omega
  obtain ⟨v, hv, hv1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hvbot
  let vb : B := ⟨v, (show starImage D.H D.V ≤ B from le_sup_right) hv⟩
  have hvT : v ∈ starImage D.H D.T := (map_mono (comap_mono h.V_le_T)) hv
  have hvR : vb ∈ (R : Subgroup B) := by rw [hR]; exact hvT
  have hevS : e vb ∈ (S : Subgroup (alternatingGroup (Fin 8))) := mem_map_of_mem _ hvR
  have hev1 : e vb ≠ 1 := fun he => hv1 (congrArg Subtype.val (e.injective (he.trans e.map_one.symm)))
  have hlN : D.L₁ ≤ normalizer (D.V : Set G) := by
    intro x hx
    exact (h.normalizer_control ⟨h.local_le (mem_sup_left hx),
      h.local_normalizes (mem_sup_left hx)⟩).2
  have hLC : localStar D ≤ centralizer (starImage D.H D.V : Set (Hstar D.H)) :=
    sup_le (Fitting.star_centralizes_V D h hindex hU D.L₁ hlN)
      (Fitting.star_centralizes_V D h hindex hU D.T h.T_normalizes_V)
  have hJ : J ≤ centralizer ({e vb} : Set (alternatingGroup (Fin 8))) := by
    rintro _ ⟨b, hb, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he : b * vb = vb * b := Subtype.ext ((mem_centralizer_iff.mp (hLC hb)) v hv).symm
    change e b * e vb = e vb * e b
    simpa only [map_mul] using congrArg e he
  exact Theory.SpecificGroups.SymmetricEight.CentralPair.pair_marking S J hSJ hne
    (e vb) hevS hev1 hJ

variable [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The A₈ natural central quotient supplies the original tilde commutator
without an additional pair-marking premise. -/
theorem alternating_eight_tilde_generation
    (s : Selected D K)
    (proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      alternatingGroup (Fin 8))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e b)
          (centralProjection D h eV u)) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ := by
  obtain ⟨g, hg⟩ := alternating_eight_pair_marking D h s hSQ hLK hm hindex hU e
  exact alternating_eight_tilde_generation_of_pair_marking D h s proper hSQ hLK hm
    hseed e eV heV g hg

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
