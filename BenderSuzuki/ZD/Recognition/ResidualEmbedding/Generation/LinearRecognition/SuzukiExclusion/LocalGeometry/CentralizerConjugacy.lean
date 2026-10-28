module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.CentralizerConjugacy.Conjugates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.CentralizerConjugacy.NormalizerCentralizer

/-!
# Centralizer equalities and the elementary Suzuki Sylow factor

Given the preceding-source Sylow configuration and normalizer control,
the conjugate-factor argument proves U elementary. The specified embedding
J → L puts the centralizer in J of each nonidentity element of U inside a
Suzuki Sylow two-subgroup. It is therefore a two-group containing U and
equals U by Sylow maximality. Normalizer control on ⟨u⟩ and the marked-center
identity C_N(A) = PJ now give C_G(A) ∩ C_G(u) = T.

The concluding theorem supplies precisely the three outstanding fields of
`LocalGeometry`. Its Sylow configuration, centralizer embedding and normalizer
control remain explicit, with their construction and final premise discharge
owned by the parent local-geometry assembly.

Source: GLS4, Chapter 2, Lemma 14.3(a,b), using Chapter 4, Lemmas 3.2(b)
and 3.6(c). No centralizer equality for arbitrary order-four elements is used.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup PFAppendixIII BenderSuzuki.MatrixGroups
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

private theorem centralizer_J_eq_U (c : SylowConfiguration M z t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : IsElementaryAbelian 2 c.U)
    {u : G} (hu : u ∈ c.U) (hne : u ≠ 1) :
    centralizer (residualGenerated M z t : Set G) ⊓ centralizer ({u} : Set G) = c.U := by
  let J := centralizer (residualGenerated M z t : Set G)
  let e : J →* SuzukiMatrixGroup m := d.model.toMonoidHom.comp f
  have hei : Function.Injective e := d.model.injective.comp hf
  let : IsElementaryAbelian 2 c.U := hU
  obtain ⟨V, hV⟩ := c.U_sylow_centralizer
  have hVU : c.U.subgroupOf J = V := by
    rw [← hV]
    exact comap_map_eq_self (by simp)
  let uJ : J := ⟨u, c.U_le_J hu⟩
  have huV : uJ ∈ (V : Subgroup J) := by
    rw [← hVU]
    exact hu
  have heune : e uJ ≠ 1 := by
    intro he
    have he' : uJ = 1 := hei (he.trans e.map_one.symm)
    exact hne (congrArg Subtype.val he')
  obtain ⟨W, hW⟩ := (V.isPGroup'.map e).exists_le_sylow
  have heW : e uJ ∈ W := hW (mem_map_of_mem e huV)
  have hbound := (suzukiSylow_borel_structure d.parameter_pos
    (MulEquiv.refl (SuzukiMatrixGroup m)) W).2.1 _ heW heune
  have hC : centralizer ({uJ} : Set J) ≤ (W : Subgroup (SuzukiMatrixGroup m)).comap e := by
    intro j hj
    exact hbound (mem_centralizer_singleton_iff.mpr
      ((show Commute j uJ from mem_centralizer_singleton_iff.mp hj).map e).eq)
  have hC2 : IsPGroup 2 (centralizer ({uJ} : Set J)) :=
    (W.isPGroup'.comap_of_injective e hei).to_le hC
  have hVC : (V : Subgroup J) ≤ centralizer ({uJ} : Set J) := by
    intro j hj
    have hjU : (j : G) ∈ c.U := hV ▸ (mem_map_of_mem J.subtype hj)
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact congrArg c.U.subtype
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative c.U)
        ⟨j, hjU⟩ ⟨u, hu⟩)
  have hCV : centralizer ({uJ} : Set J) = V := V.is_maximal' hC2 hVC
  ext j
  constructor
  · rintro ⟨hjJ, hjC⟩
    have hj : (⟨j, hjJ⟩ : J) ∈ centralizer ({uJ} : Set J) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hjC))
    rw [hCV] at hj
    rw [← hV]
    exact ⟨⟨j, hjJ⟩, hj, rfl⟩
  · intro hj
    refine ⟨c.U_le_J hj, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg c.U.subtype
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative c.U)
        ⟨j, hj⟩ ⟨u, hu⟩)

/-- The second equality of Lemma 14.3(a), after the conjugate-factor argument
has established exponent two. -/
public theorem Context.centralizer_U (c : SylowConfiguration M z t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f)
    (hcontrol : ∀ Y : Subgroup G,
      Y ≤ centralizer (residualGenerated M z t : Set G) → Y ≠ ⊥ →
        normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G)) :
    ∀ u ∈ c.U, u ≠ 1 →
      centralizer (closure (Z ∩ (M : Set G)) : Set G) ⊓ centralizer ({u} : Set G) = c.T := by
  let : IsElementaryAbelian 2 c.U := d.U_elementary c hcontrol
  intro u hu hne
  have hJu := centralizer_J_eq_U d c f hf inferInstance hu hne
  have hcyc : zpowers u ≠ ⊥ := by
    intro he
    exact hne (mem_bot.mp (he ▸ mem_zpowers u))
  have hCN : centralizer ({u} : Set G) ≤ normalizer (residualGenerated M z t : Set G) := by
    have hh := (Subgroup.centralizer_le_normalizer (zpowers u : Set G)).trans
      (hcontrol _ (zpowers_le.mpr (c.U_le_J hu)) hcyc)
    rwa [zpowers_eq_closure, centralizer_closure] at hh
  have hPCu : borelTwoCore M z t ≤ centralizer ({u} : Set G) := by
    intro p hp
    exact mem_centralizer_singleton_iff.mpr (c.U_le_J hu p (c.P_le_L hp))
  have hUCu : c.U ≤ centralizer ({u} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (congrArg c.U.subtype
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative c.U) ⟨v, hv⟩ ⟨u, hu⟩))
  apply le_antisymm
  · rintro x ⟨hxA, hxu⟩
    have hxPJ := (Set.ext_iff.mp d.centralizer_in_normalizer x).mp ⟨hCN hxu, hxA⟩
    obtain ⟨p, hp, j, hj, he⟩ := Set.mem_mul.mp hxPJ
    have hjCu : j ∈ centralizer ({u} : Set G) := by
      have he' : j = p⁻¹ * x := by rw [← he]; group
      rw [he']
      exact (centralizer _).mul_mem ((centralizer _).inv_mem (hPCu hp)) hxu
    have hjU : j ∈ c.U := by rw [← hJu]; exact ⟨hj, hjCu⟩
    rw [← he]
    exact c.T.mul_mem (c.P_le_T hp) (c.U_le_T hjU)
  · intro x hxT
    have hxprod : x ∈ (borelTwoCore M z t : Set G) * (c.U : Set G) := by
      rw [← c.T_product]
      exact hxT
    obtain ⟨p, hp, v, hv, he⟩ := Set.mem_mul.mp hxprod
    have hxPJ : x ∈ (borelTwoCore M z t : Set G) *
        (centralizer (residualGenerated M z t : Set G) : Set G) :=
      Set.mem_mul.mpr ⟨p, hp, v, c.U_le_J hv, he⟩
    refine ⟨((Set.ext_iff.mp d.centralizer_in_normalizer x).mpr hxPJ).2, ?_⟩
    rw [← he]
    exact (centralizer _).mul_mem (hPCu hp) (hUCu hv)
/-- The three centralizer/conjugacy outputs, with exactly the literal fields
of `LocalGeometry` and only the preceding-source inputs of this helper. -/
public theorem Context.centralizer_conjugacy
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (c : SylowConfiguration M z t)
    (hcontrol : ∀ Y : Subgroup G,
      Y ≤ centralizer (residualGenerated M z t : Set G) → Y ≠ ⊥ →
        normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G)) :
    (((normalizer (residualGenerated M z t : Set G) ⊓
      centralizer (closure (Z ∩ (M : Set G)) : Set G) : Subgroup G) : Set G) =
      (borelTwoCore M z t : Set G) *
        (centralizer (residualGenerated M z t : Set G) : Set G)) ∧
    (∀ u ∈ c.U, u ≠ 1 →
      centralizer (closure (Z ∩ (M : Set G)) : Set G) ⊓
        centralizer ({u} : Set G) = c.T) ∧
    IsElementaryAbelian 2 c.U :=
  ⟨d.centralizer_in_normalizer, d.centralizer_U c f hf hcontrol,
    d.U_elementary c hcontrol⟩

end BenderSuzuki.ZD.SuzukiExclusion
