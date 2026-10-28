module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PartitionReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Natural
/-!
# Excluding case (1) of 13.8.8 in the A₇ branch

A genuine transvection actor triggers the full group alternatives of 13.8.5.
The seven-point cardinal bounds select its natural S₇ model. The earlier
triple-cover marking L₁/O₂(L₁) ≃ E₉ gives the factor of nine, forcing the
four-plus-three partition after the solvable-overgroup and theta argument.
The same coordinate change transports the natural module. F.9.13 places
an actual conjugate of Vδ in the local two-core, so the existing parity
obstruction contradicts the transvection in A ≤ Vδ.

The source application takes A = Uβ ≤ Vβ or A = Vγ. This theorem constructs
the natural embedding and full partition image required by the obstruction;
neither a partition contradiction nor the chosen partition is an input.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.5, 13.8.8(1), F.9.13(1–2), and the first paragraph of 13.8.24,
printed pp.947–949, 958 (1 March 2004 manuscript).
-/

public section
open Subgroup Equiv BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

omit [Finite G] in
/-- In the triple-cover case the source's actual L₁/O₂(L₁) ≃ E₉
supplies the factor of nine used in the partition calculation. -/
theorem nine_dvd_of_elementary_nine_quotient (L₁ : Subgroup G)
    (e : (L₁ ⧸ pCore 2 L₁) ≃* Multiplicative (Fin 2 → ZMod 3)) :
    9 ∣ Nat.card L₁ := by
  have hc : Nat.card (L₁ ⧸ pCore 2 L₁) = 9 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  rw [← hc]
  exact card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L₁))
    (QuotientGroup.mk'_surjective _)

/-- The first source case is impossible for its actual elementary actor A≤V.
The natural identification is selected from all three 13.8.5 group alternatives;
13.8.13 and theta construct the partition equality; the factor of nine rules
out the pair partition; finally F.9.13 supplies the actual conjugated actor. -/
theorem exclude_first_case_actor
    (H L L₁ T G₁ M A V : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) E)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (h5 : ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim ρ (zpowers a) = 1 →
      TransvectionModels ρ L)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* Multiplicative (Fin 2 → ZMod 3)))
    (hVH : V ≤ H) (hAV : A ≤ V) [IsElementaryAbelian 2 A]
    (hy : ∃ y : H, V.map (MulAut.conj (y : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (ht : ∃ a ∈ Source.starImage H A, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) : False := by
  obtain ⟨a, ha, hn, ht1⟩ := ht
  obtain ⟨hc, hnat⟩ := seven_natural_of_transvection_models ρ L φ hφ hAlt
    (h5 a hn ht1)
  obtain ⟨e, c, he⟩ := hnat
  obtain ⟨eL₁⟩ := hcover hc
  have h9 := nine_dvd_of_elementary_nine_quotient L₁ eL₁
  have hAe : alternatingGroup (Fin 7) ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  obtain ⟨σ, hp, _, _, _⟩ := source_partition_dichotomy H L₁ T G₁ M hbase hHG
    htheta h13 e.toMonoidHom e.injective hAe S hS
  let ψ := (MulAut.conj σ).toMonoidHom.comp e.toMonoidHom
  have hi : Function.Injective ψ := (MulAut.conj σ).injective.comp e.injective
  have hs : Function.Surjective ψ := (MulAut.conj σ).surjective.comp e.surjective
  have hp4 : Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap ψ := by
    rcases hp with hp | hp
    · exact hp
    · exact (not_pair_partition_of_nine H L₁ T (le_sup_left.trans hbase) ψ hi
        h9 hp).elim
  have hm : HasNaturalSubmodule ρ ψ := naturalSubmodule_conjugate ρ e.toMonoidHom
    ⟨c.toLinearMap, c.injective, he⟩ σ
  obtain ⟨y, hy⟩ := hy
  apply no_ambient_conjugated_transvection H (L₁ ⊔ T) A V hbase hVH hAV ρ ψ hi hm
    _ y hy ⟨a, ha, hn, ht1⟩
  rw [hp4, map_comap_eq_self_of_surjective hs]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
