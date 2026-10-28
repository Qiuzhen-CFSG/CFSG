module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CoreCrossingSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AutomizerIndexSource
public import Theory.GroupTheory.AbelianCrossingKernel
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowModels

/-!
# Excluding the abelian source core of order greater than two

The original central line shows that a core larger than two is noncentral
in the actual Sylow. The genuine component/core index gives an index-two
commuting product, and the original crossing-core theorem supplies the
normal disjoint conjugate. The checked dihedral and semidihedral exponent
obstruction excludes an abelian core. The final model wrappers construct
the quotient maps, their Sylow images and the nonabelian component Sylow.

The order-two core exclusion is the preceding independent source branch;
it is deliberately retained here as the hypothesis that the core is larger
than two. Source: Aschbacher--Smith 2.5.21, printed p.565.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open scoped Pointwise
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Transfer the original component/core index to the literal Sylow product. -/
theorem MathieuSourceSetup.sylow_core_index_le_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hi : (K ⊔ twoCore H).relIndex H ≤ 2) :
    ((twoCore H).subgroupOf ((S : Subgroup H).map H.subtype) ⊔
      K.subgroupOf ((S : Subgroup H).map H.subtype)).index ≤ 2 := by
  let Y := (S : Subgroup H).map H.subtype
  have hCY : twoCore H ≤ Y := by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_left
  have hCK : twoCore H ≤ centralizer (K : Set G) := by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_right
  have he : (K ⊔ twoCore H).subgroupOf Y = (twoCore H).subgroupOf Y ⊔ K.subgroupOf Y := by
    apply le_antisymm
    · intro y hy
      have hm : (y : G) ∈ (K : Set G) * (twoCore H : Set G) := by
        rwa [← coe_mul_of_right_le_normalizer_left K (twoCore H)
          (hCK.trans (Subgroup.centralizer_le_normalizer _))]
      obtain ⟨k, hk, u, hu, hku⟩ := hm
      have hkY : k ∈ Y := by
        have hh := Y.mul_mem y.property (Y.inv_mem (hCY hu))
        rwa [← hku, mul_inv_cancel_right] at hh
      have hh := ((twoCore H).subgroupOf Y ⊔ K.subgroupOf Y).mul_mem
        (mem_sup_right (show (⟨k, hkY⟩ : Y) ∈ K.subgroupOf Y from hk))
        (mem_sup_left (show (⟨u, hCY hu⟩ : Y) ∈ (twoCore H).subgroupOf Y from hu))
      exact (show (⟨k, hkY⟩ : Y) * ⟨u, hCY hu⟩ = y from Subtype.ext hku) ▸ hh
    · apply sup_le
      · exact comap_mono le_sup_right
      · exact comap_mono le_sup_left
  rw [← he]
  exact (relIndex_le_of_le_right (map_subtype_le _) (by exact index_ne_zero_of_finite)).trans hi

/-- The original center line makes a core of order greater than two noncentral in S. -/
theorem MathieuSourceSetup.large_twoCore_not_central
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hlarge : 2 < Nat.card (twoCore H)) :
    ¬ (twoCore H).subgroupOf ((S : Subgroup H).map H.subtype) ≤
      center ((S : Subgroup H).map H.subtype) := by
  let Y := (S : Subgroup H).map H.subtype
  have hCY : twoCore H ≤ Y := pCoreIn_le_sylow H S
  obtain ⟨t, _, ht, _, _, hline, _⟩ := MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  intro hcent
  have hC : twoCore H ≤ centerIn Y := by
    intro u hu
    exact ⟨hCY hu, fun v hv => congrArg Subtype.val
      (mem_center_iff.mp (hcent (show (⟨u, hCY hu⟩ : Y) ∈ (twoCore H).subgroupOf Y from hu)) ⟨v, hv⟩)⟩
  have he : twoCore H = zpowers t := (inf_eq_right.mpr hC).symm.trans hline
  rw [he, Nat.card_zpowers, ht] at hlarge
  omega
/-- Original source 2.5.21 excludes an abelian core once its order exceeds two. -/
theorem MathieuSourceSetup.twoCore_not_commutative_of_large
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (f : H →* Q)
    (hker : f.ker = (((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)).subgroupOf H)
    (hmodel : (∃ n : ℕ, Nonempty ((S : Subgroup H).map f ≃* DihedralGroup (2 ^ n))) ∨
      Nonempty ((S : Subgroup H).map f ≃* Semidihedral.StandardModel 4 (by decide)))
    (hi : (K ⊔ twoCore H).relIndex H ≤ 2)
    (hlarge : 2 < Nat.card (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G)) :
    ¬ IsMulCommutative (twoCore H) := by
  intro hcomm
  let := hcomm
  let Y := (S : Subgroup H).map H.subtype
  let C := (twoCore H).subgroupOf Y
  let D := K.subgroupOf Y
  let : IsMulCommutative C := inferInstance
  have hYH : Y ≤ H := map_subtype_le _
  have hcore := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hCY : twoCore H ≤ Y := hcore ▸ inf_le_left
  let q : Y →* (S : Subgroup H).map f :=
    (f.comp (inclusion hYH)).codRestrict _ (by
      intro y
      refine ⟨⟨y, hYH y.property⟩, ?_, rfl⟩
      obtain ⟨u, hu, he⟩ := y.property
      exact (show u = (⟨y, hYH y.property⟩ : H) from Subtype.ext he) ▸ hu)
  have hq : Function.Surjective q := by
    rintro ⟨v, u, hu, rfl⟩
    refine ⟨⟨u, mem_map_of_mem H.subtype hu⟩, Subtype.ext ?_⟩
    rfl
  have hk : q.ker = C := by
    ext y
    change q y = 1 ↔ (y : G) ∈ twoCore H
    constructor
    · intro hy
      have hh : (⟨y, hYH y.property⟩ : H) ∈ f.ker := congrArg Subtype.val hy
      rw [hker] at hh
      exact hcore.symm ▸ hh
    · intro hy
      apply Subtype.ext
      have hh : (⟨y, hYH y.property⟩ : H) ∈ f.ker := by
        rw [hker]
        exact hcore ▸ hy
      exact hh
  have hCD : Disjoint C D := by
    apply disjoint_def.mpr
    intro y hyC hyD
    have hyc : (y : G) ∈ centralizer (K : Set G) := by
      have hh : (y : G) ∈ twoCore H := hyC
      rw [hcore] at hh
      exact hh.2
    have hz : (⟨y, hyD⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun k => Subtype.ext (hyc k k.property))
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen, mem_bot] at hz
    exact Subtype.ext (congrArg (fun k : K => (k : G)) hz)
  have hDC : D ≤ centralizer (C : Set Y) := by
    intro d hd u hu
    have hh : (u : G) ∈ twoCore H := hu
    rw [hcore] at hh
    exact Subtype.ext (hh.2 d hd).symm
  have hnC : ¬ C ≤ center Y := MathieuSourceSetup.large_twoCore_not_central c hG hempty hgen hb hlarge
  have hiC : (C ⊔ D).index ≤ 2 := MathieuSourceSetup.sylow_core_index_le_two c hgen hi
  have hnD' : ¬ IsMulCommutative D := by
    intro hh
    apply hnD
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact congrArg (fun y : D => (y : Y).val)
      (hh.is_comm.comm (⟨⟨a, a.property.1⟩, a.property.2⟩ : D)
        ⟨⟨b, b.property.1⟩, b.property.2⟩)
  obtain ⟨x, hxT, hxS, hxN, hx2⟩ := exists_outside_normalizer_square_mem Y
    (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  have hd := generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le, c.component⟩ hgen hxT hxS hxN hx2
  let a : MulAut Y := Y.normalizerMonoidHom ⟨x⁻¹, (normalizer (Y : Set G)).inv_mem hxN⟩
  have ha (y : Y) : (a y : G) = x⁻¹ * y * x := by
    simp only [a, normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hX (y : Y) (hy : y ∈ C.map a.toMonoidHom) : (y : G) ∈ (twoCore H).conjBy x⁻¹ := by
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨(w : G), hw, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using (ha w).symm
  have hCX : Disjoint C (C.map a.toMonoidHom) := by
    apply disjoint_def.mpr
    intro y hyC hyX
    exact Subtype.ext (disjoint_def.mp hd.1 hyC (hX y hyX))
  have hXC : C.map a.toMonoidHom ≤ centralizer (C : Set Y) := by
    intro y hy u hu
    exact Subtype.ext ((hd.2.1 hu) _ (hX y hy)).symm
  have hke {R : Type} [Group R] (e : (S : Subgroup H).map f ≃* R) :
      (e.toMonoidHom.comp q).ker = C := by
    ext y
    change e (q y) = 1 ↔ y ∈ C
    rw [e.map_eq_one_iff]
    exact show q y = 1 ↔ y ∈ C from Iff.of_eq (congrArg (fun B : Subgroup Y => y ∈ B) hk)
  rcases hmodel with hd | hs
  · obtain ⟨n, ⟨e⟩⟩ := hd
    exact abelian_crossing_kernel_dihedral_impossible (e.toMonoidHom.comp q)
      (e.surjective.comp hq) C D (hke e) hCD hDC hiC hnC hnD' a hCX hXC
  · obtain ⟨e⟩ := hs
    exact abelian_crossing_kernel_semidihedral_impossible (e.toMonoidHom.comp q)
      (e.surjective.comp hq) C D (hke e) hCD hDC hiC hnC hnD' a hCX hXC

/-- The PGL₂ source discharges its quotient-map and model premises internally. -/
theorem MathieuSourceSetup.pgl_source_twoCore_noncommutative
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {F : Type*} [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 F)
    (hi : (K ⊔ twoCore H).relIndex H ≤ 2)
    (hlarge : 2 < Nat.card (twoCore H))
    (hnD : ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G)) :
    ¬ IsMulCommutative (twoCore H) := by
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨n, _, ⟨eP⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hodd
    (S.mapSurjective hf)
  exact MathieuSourceSetup.twoCore_not_commutative_of_large c hG hempty hgen hb f hk
    (Or.inl ⟨n, ⟨eP⟩⟩) hi hlarge hnD

/-- The M₁₀ branch supplies both index two and the nonabelian component Sylow. -/
theorem MathieuSourceSetup.m10_source_twoCore_noncommutative
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension)
    (hlarge : 2 < Nat.card (twoCore H)) : ¬ IsMulCommutative (twoCore H) := by
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  have hi := MathieuSourceSetup.alternating_six_nonfull_core_index c hG hempty hgen eK (Or.inl ⟨eQ⟩)
  exact MathieuSourceSetup.twoCore_not_commutative_of_large c hG hempty hgen hb f hk
    (Or.inr ⟨AlternatingSix.M10.sylowTwoEquivSemidihedral (S.mapSurjective hf)⟩) hi.le hlarge
    (MathieuSourceSetup.alternating_component_sylow_noncommutative c eK)

/-- The prime PGL₂ branch discharges its index and component Sylow from the original model. -/
theorem MathieuSourceSetup.prime_pgl_source_twoCore_noncommutative
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 (ZMod p))
    (hlarge : 2 < Nat.card (twoCore H)) : ¬ IsMulCommutative (twoCore H) := by
  have ho : Odd p := hfm.1.odd_of_ne_two (by omega)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by decide, by simp⟩
  have hi := MathieuSourceSetup.linear_pgl_core_index c hG hempty hgen (ZMod p) (by simpa using ho) eK eQ
  exact MathieuSourceSetup.pgl_source_twoCore_noncommutative c hG hempty hgen hb hodd eQ hi.le hlarge
    (MathieuSourceSetup.fermat_mersenne_component_sylow_noncommutative c hp hfm eK)

/-- The PGL₂(9) branch discharges both source-model inputs. -/
theorem MathieuSourceSetup.alternating_pgl_source_twoCore_noncommutative
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
    (hlarge : 2 < Nat.card (twoCore H)) : ¬ IsMulCommutative (twoCore H) := by
  have hi := MathieuSourceSetup.alternating_six_nonfull_core_index c hG hempty hgen eK (Or.inr ⟨eQ⟩)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card Atlas.Comparisons.Exceptional.Nine.F) :=
    ⟨3, 2, by decide, by decide, by decide, Atlas.Comparisons.Exceptional.Nine.card⟩
  exact MathieuSourceSetup.pgl_source_twoCore_noncommutative c hG hempty hgen hb hodd eQ hi.le hlarge
    (MathieuSourceSetup.alternating_component_sylow_noncommutative c eK)


/-- The prime PSL₂ quotient branch also excludes an abelian large core. -/
theorem MathieuSourceSetup.prime_psl_source_twoCore_noncommutative
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (hlarge : 2 < Nat.card (twoCore H)) : ¬ IsMulCommutative (twoCore H) := by
  have ho : Odd p := hfm.1.odd_of_ne_two (by omega)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by decide, by simp⟩
  have hi := MathieuSourceSetup.normal_component_core_index_le_two_of_card c hG hempty hgen (by
    rw [Nat.card_congr eK.toEquiv, Nat.card_congr eQ.toEquiv]
    omega)
  obtain ⟨f, hf, hk⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  obtain ⟨n, _, ⟨eP⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod p) hodd
    (S.mapSurjective hf)
  exact MathieuSourceSetup.twoCore_not_commutative_of_large c hG hempty hgen hb f hk
    (Or.inl ⟨n, ⟨eP⟩⟩) hi hlarge
    (MathieuSourceSetup.fermat_mersenne_component_sylow_noncommutative c hp hfm eK)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
