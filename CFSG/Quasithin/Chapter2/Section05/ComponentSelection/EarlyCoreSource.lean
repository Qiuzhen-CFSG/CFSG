module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AbelianCoreSource

/-!
# The original large-core branch and marked involutions

The order-two exclusion combines with the original central line to make
the core larger than two. The preceding abelian-core contradiction then
makes it nonabelian. Concrete model wrappers supply the component Sylow,
so the original crossing construction gives tˣ=zK and z=t*zK, retaining
nonfusion and the actual Sylow of C_G(t). In the M₁₀ case the quaternion
terminal leaves only dihedral eight and semidihedral sixteen.

All conclusions are on the original source subgroups and marks. The
independent |SC|=2 exclusion and the later 2.5.19 component-centralizer
argument remain distinct source steps. Source: Aschbacher--Smith 2.5.21,
printed pp.565--566.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original nontrivial center line upgrades the order-two exclusion to the large-core branch. -/
theorem MathieuSourceSetup.two_lt_core_card_of_ne_two
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hne : Nat.card (twoCore H) ≠ 2) : 2 < Nat.card (twoCore H) := by
  obtain ⟨t, _, ht, _, htC, _⟩ := MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have hd : 2 ∣ Nat.card (twoCore H) := by
    have hh := orderOf_dvd_natCard (⟨t, htC⟩ : twoCore H)
    rwa [← orderOf_coe, ht] at hh
  have hp := Nat.card_pos (α := twoCore H)
  have hle := Nat.le_of_dvd hp hd
  omega

/-- In the PGL case a nonabelian source core is dihedral of order at least eight. -/
theorem MathieuSourceSetup.pgl_nonabelian_twoCore_model
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    {F : Type*} [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 F)
    (hn : ¬ IsMulCommutative (twoCore H)) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)) := by
  obtain hc | ⟨k, ⟨e⟩⟩ := MathieuSourceSetup.pgl_twoCore_models c hgen hodd eQ
  · exact (hn hc.isMulCommutative).elim
  refine ⟨k, ?_, ⟨e⟩⟩
  by_contra! hk
  have hh : IsMulCommutative (DihedralGroup (2 ^ k)) := by
    apply DihedralGroup.commutative_iff.mpr
    interval_cases k <;> decide
  apply hn
  exact ⟨⟨fun a b => e.injective (by simpa only [map_mul] using hh.is_comm.comm (e a) (e b))⟩⟩

/-- The M₁₀ source has only dihedral eight or semidihedral sixteen once the core is large. -/
theorem MathieuSourceSetup.m10_large_twoCore_models
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension)
    (hlarge : 2 < Nat.card (twoCore H)) :
    Nonempty (twoCore H ≃* DihedralGroup 4) ∨
      Nonempty (twoCore H ≃* Semidihedral.StandardModel 4 (by decide)) := by
  have hn := MathieuSourceSetup.m10_source_twoCore_noncommutative c hG hempty hgen hb eK eQ hlarge
  rcases MathieuSourceSetup.m10_twoCore_models c hgen eK eQ with hc | hr
  · exact (hn hc.isMulCommutative).elim
  rcases hr with hfour | hr
  · let := hfour
    exact (hn IsKleinFour.isMulCommutative).elim
  exact hr
/-- The original M₁₀ large-core branch constructs the marked crossing with no nonabelianness premise. -/
theorem MathieuSourceSetup.m10_large_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension)
    (hlarge : 2 < Nat.card (twoCore H)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  exact MathieuSourceSetup.m10_source_nonabelian_crossing c hG hempty hgen hb
    (MathieuSourceSetup.m10_source_twoCore_noncommutative c hG hempty hgen hb eK eQ hlarge)
    (MathieuSourceSetup.alternating_component_sylow_noncommutative c eK) eQ

/-- The PGL₂(9) source constructs the same original crossing marks. -/
theorem MathieuSourceSetup.alternating_pgl_large_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
    (hlarge : 2 < Nat.card (twoCore H)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card Atlas.Comparisons.Exceptional.Nine.F) :=
    ⟨3, 2, by decide, by decide, by decide, Atlas.Comparisons.Exceptional.Nine.card⟩
  exact MathieuSourceSetup.pgl_source_nonabelian_crossing c hG hempty hgen hb
    (MathieuSourceSetup.alternating_pgl_source_twoCore_noncommutative c hG hempty hgen hb eK eQ hlarge)
    (MathieuSourceSetup.alternating_component_sylow_noncommutative c eK) hodd eQ

/-- The prime PGL₂ source constructs the crossing marks from its literal prime parameter. -/
theorem MathieuSourceSetup.prime_pgl_large_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p))
    (hlarge : 2 < Nat.card (twoCore H)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  have ho : Odd p := hfm.1.odd_of_ne_two (by omega)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by decide, by simp⟩
  exact MathieuSourceSetup.pgl_source_nonabelian_crossing c hG hempty hgen hb
    (MathieuSourceSetup.prime_pgl_source_twoCore_noncommutative c hG hempty hgen hb hp hfm eK eQ hlarge)
    (MathieuSourceSetup.fermat_mersenne_component_sylow_noncommutative c hp hfm eK) hodd eQ

/-- The prime PSL₂ quotient source constructs the same crossing marks. -/
theorem MathieuSourceSetup.prime_psl_large_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (hlarge : 2 < Nat.card (twoCore H)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  have ho : Odd p := hfm.1.odd_of_ne_two (by omega)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by decide, by simp⟩
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨_, _, ⟨eP⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod p) hodd
    (S.mapSurjective hf)
  exact MathieuSourceSetup.source_nonabelian_crossing c hG hempty hgen hb f hk
    (MathieuSourceSetup.prime_psl_source_twoCore_noncommutative c hG hempty hgen hb hp hfm eK eQ hlarge)
    (MathieuSourceSetup.fermat_mersenne_component_sylow_noncommutative c hp hfm eK)
    (exists_abelian_index_two_of_dihedral eP)

/-- The binary linear row supplies its own PGL₂(7) automizer and the original crossing marks. -/
theorem MathieuSourceSetup.linear_binary_large_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* Matrix.PSL3Two.PSL)
    (hlarge : 2 < Nat.card (twoCore H)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨eQ⟩ := MathieuSourceSetup.normal_linear_binary_core_quotient c hG hempty hgen eK
  have hfm : IsFermatOrMersennePrime 7 := ⟨by decide, Or.inr ⟨3, by decide⟩⟩
  exact MathieuSourceSetup.prime_pgl_large_core_crossing c hG hempty hgen hb
    (p := 7) (by decide) hfm
    (eK.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm)
    (eQ.trans Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut.symm) hlarge

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
