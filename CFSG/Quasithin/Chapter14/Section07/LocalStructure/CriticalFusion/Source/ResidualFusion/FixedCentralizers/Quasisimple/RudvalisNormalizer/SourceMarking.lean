module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer.Transport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.POrder
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound
public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Generation and marking of the original eight in the Rudvalis cover

The natural action of the original L on V maps its point stabilizer onto the
binary point stabilizer. Its two-residual is exactly the image of the original
L₁. A cubic element and a conjugate supply displacements spanning all three
coordinates, proving V = [V,L₁]. Since L₁ lies in K = O²(H), this places V in K
and hence in the supplied component Lᵤ.

Restrict the actual Sylow subgroup C_T(u) of C_G(u) to the relatively normal
component. Its image under the recognized cover is Sylow in the literal
Rudvalis model and normalizes the image of V. The covering line meets V
trivially, so this image is elementary of order eight. After Sylow conjugacy,
the checked normal elementary catalogue identifies it with `elementary 2`.
The change of coordinates is exactly `FixedRudvalisCover.align` and thus
preserves the specified kernel.

The final theorem retains the original source hypotheses and supplies the
generation and marking inputs to the independent complement argument. It
proves this placement, not the remaining complement-normalization argument.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 14.7.68(2),
printed p.1071 (PDF p.1088), especially the original L₁-invariant complement
in ⟨u⟩V. The Rudvalis carrier and certificates retain their ATLAS attribution
in the imported model modules.
-/

@[expose] public section
noncomputable section

open Subgroup
open scoped commutatorElement IsMulCommutative
open BinaryLinear.OuterCyclic BinaryLinear.CubicPairNormalizers.CoreAbsorption

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.RudvalisSourceMarking
private abbrev E := Space 3
private abbrev unitVector (i : Fin 3) : E := Pi.single i 1
private abbrev P : Subgroup (LinearGroup 3) := MulAction.stabilizer (LinearGroup 3) (unitVector 0)
private abbrev R : Subgroup (LinearGroup 3) := (pResidual 2 P).map P.subtype

private theorem displacement_span (S : Submodule (ZMod 2) E)
    (hS : ∀ a ∈ R, ∀ x : E, a x - x ∈ S) : S = ⊤ := by
  let c : LinearGroup 3 := cubic 1 2 (by decide)
  let t : LinearGroup 3 := root 0 1 (by decide) 1
  have hcP : c ∈ P := by
    change c (unitVector 0) = unitVector 0
    ext k
    fin_cases k <;> simp [c, cubic, root_apply, unitVector]
  have htP : t ∈ P := by
    change t (unitVector 0) = unitVector 0
    ext k
    fin_cases k <;> simp [t, root_apply, unitVector]
  have hcR : c ∈ R := by
    refine mem_map.mpr ⟨⟨c, hcP⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (show (⟨c, hcP⟩ : P) ^ 3 = 1 from
        Subtype.ext (cubic_cube 1 2 (by decide))))
  have htcR : t * c * t⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (le_normalizer_embedded_pResidual 2 P htP) c).mp hcR
  have he1 : unitVector 1 ∈ S := by
    have h := hS c hcR (unitVector 2)
    convert h using 1
    ext k
    fin_cases k <;> simp [c, cubic, root_apply, unitVector]
  have he2 : unitVector 2 ∈ S := by
    have h := S.add_mem (hS c hcR (unitVector 1)) he1
    convert h using 1
    ext k
    fin_cases k <;> simp [c, cubic, root_apply, unitVector]
  have he0 : unitVector 0 ∈ S := by
    have h := S.add_mem (hS (t * c * t⁻¹) htcR (unitVector 2)) he1
    convert h using 1
    ext k
    fin_cases k <;> simp [c, t, cubic, root_apply, unitVector]
  apply top_unique
  intro x _
  have he : x = x 0 • unitVector 0 + x 1 • unitVector 1 + x 2 • unitVector 2 := by
    ext k
    fin_cases k <;> simp [unitVector]
  rw [he]
  exact S.add_mem (S.add_mem (S.smul_mem _ he0) (S.smul_mem _ he1)) (S.smul_mem _ he2)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.RudvalisSourceMarking

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open BinaryLinear.SmallParabolicLevi RudvalisSourceMarking
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

include d in
/-- The genuine point-parabolic action generates the original V by its
original L₁-commutators. The covering group is not needed for this identity. -/
theorem seed_eq_commutator_pointResidual : V = ⁅V, F.Li L 1⁆ := by
  let := d.natural.chosen.elementary
  let A := d.natural.naturalMarking.geometryAction
  let c₀ := d.natural.naturalMarking.coordinates
  let z : Additive V := Additive.ofMul ⟨d.z, F.le_seed 1 (d.point ▸ mem_zpowers d.z)⟩
  have hz : z ≠ 0 := fun h => d.z_ne_one (congrArg (fun v : Additive V => (v.toMul : G)) h)
  obtain ⟨a, ha⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq
    (show c₀ z ≠ 0 from fun h => hz (c₀.injective (h.trans c₀.map_zero.symm))) (show unitVector 0 ≠ 0 by intro h; have := congrFun h 0; simp [unitVector] at this)
  let c : Additive V ≃ₗ[ZMod 2] E := c₀.trans a
  have hcz : c z = unitVector 0 := ha
  let f : L →* LinearGroup 3 := (linearGroupCongr c).toMonoidHom.comp A.action
  have hf : Function.Surjective f := (linearGroupCongr c).surjective.comp A.surjective
  have hact (l : L) (v : Additive V) :
      f l (c v) = c (A.action l v) := by simp [f, linearGroupCongr_apply]
  let N := (L ⊓ F.H : Subgroup G).subgroupOf L
  have hN : N.map f = P := by
    ext b
    obtain ⟨l, rfl⟩ := hf b
    have he : f l ∈ P ↔ (l : G) ∈ F.H := by
      change f l (unitVector 0) = unitVector 0 ↔ _
      rw [← hcz, hact, c.injective.eq_iff, d.centralizer_eq]
      rw [mem_centralizer_singleton_iff]
      constructor
      · intro h
        have hh := congrArg (fun v : Additive V => (v.toMul : G)) h
        rw [A.conjugation] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      · intro h
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [A.conjugation]
        change (l : G) * d.z * (l : G)⁻¹ = d.z
        rw [h, mul_inv_cancel_right]
    constructor
    · rintro ⟨k, hk, hkl⟩
      -- The action kernel is contained in the point stabilizer.
      have hkP := (show f k ∈ P from (by
        have heK : f k (unitVector 0) = unitVector 0 := by
          rw [← hcz, hact]
          apply congrArg c
          apply Additive.toMul.injective
          apply Subtype.ext
          rw [A.conjugation]
          have hkc := mem_centralizer_singleton_iff.mp (d.centralizer_eq ▸ hk.2)
          change (k : G) * d.z * (k : G)⁻¹ = d.z
          exact (mul_inv_eq_iff_eq_mul).mpr hkc
        exact heK))
      exact hkl ▸ hkP
    · intro hl
      exact mem_map.mpr ⟨l, ⟨l.property, he.mp hl⟩, rfl⟩
  let B := (pResidual 2 N).map N.subtype
  have hB : B.map f = R := by rw [map_embedded_pResidual, hN]
  have hBG : B.map L.subtype = F.Li L 1 := by
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le (show L ⊓ F.H ≤ L from inf_le_left)]
    rfl
  let C := ⁅V, F.Li L 1⁆
  let S : Submodule (ZMod 2) E := (NormalGeometry.space (V := V) C).map c.toLinearMap
  have hdisp : ∀ b ∈ R, ∀ x : E, b x - x ∈ S := by
    intro b hb x
    obtain ⟨l, hl, rfl⟩ := mem_map.mp (hB.symm ▸ hb)
    let v := c.symm x
    refine Submodule.mem_map.mpr ⟨A.action l v - v, ?_, ?_⟩
    · rw [NormalGeometry.mem_space]
      change ((A.action l v).toMul : G) / (v.toMul : G) ∈ C
      rw [div_eq_mul_inv, A.conjugation]
      exact (commutator_comm (F.Li L 1) V).le
        (commutator_mem_commutator (hBG ▸ mem_map_of_mem L.subtype hl) v.toMul.property)
    · change c (A.action l v - v) = _
      rw [map_sub, ← hact, c.apply_symm_apply]
  have hS : S = ⊤ := displacement_span S hdisp
  apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp
    ((F.Li_le L 1).trans (inf_le_left.trans d.natural.chosen.normalizes)))
  intro v hv
  have hm : c (Additive.ofMul ⟨v, hv⟩) ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hm
  have he' : w = Additive.ofMul ⟨v, hv⟩ := c.injective he
  have hw' : (w.toMul : G) ∈ C := hw
  rw [he'] at hw'
  exact hw'

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source


open Subgroup
open scoped Pointwise IsMulCommutative
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}

private theorem localP_odd_index : ¬ 2 ∣ localP.index := by
  intro h
  apply Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
  rw [← localP.card_mul_index, IntrinsicSylow.localP_card]
  exact Nat.mul_dvd_mul_left 16384 h

private def modelSylow : Sylow 2 Rudvalis.Model :=
  IntrinsicSylow.localP_isPGroup.toSylow localP_odd_index

private theorem seed_le_fixedSylow (d : Data T L V F W) (u : F.U) : V ≤ d.fixedSylow u := by
  let := d.abelian
  refine le_inf d.natural.chosen.le_sylow ?_
  intro v hv
  exact mem_centralizer_singleton_iff.mpr
    (setLike_mul_comm (V_le_U F hv) u.property)

private theorem marking_of_containment
    (earlier : d.ModuleSeparation) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal) (hout : ¬ Lu ≤ F.H)
    (r : d.FixedRudvalisCover u Lu) (hV : V ≤ Lu) :
    ∃ g : Rudvalis.Model, (V.subgroupOf Lu).map (r.align g).projection = elementary 2 := by
  let := d.natural.chosen.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf Lu) := IsElementaryAbelian.subgroupOf hV
  obtain ⟨S, hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsyl hLu hn.isSubnormal
  have hVS : V.subgroupOf Lu ≤ (S : Subgroup Lu) := by
    intro v hv
    have hm : (v : G) ∈ (S : Subgroup Lu).map Lu.subtype :=
      hS.symm ▸ (show (v : G) ∈ d.fixedSylow u ⊓ Lu from
        ⟨seed_le_fixedSylow d u hv, v.property⟩)
    obtain ⟨s, hs, he⟩ := mem_map.mp hm
    exact (Subtype.ext he : s = v) ▸ hs
  have hSn : (S : Subgroup Lu) ≤ normalizer (V.subgroupOf Lu : Set Lu) := by
    rw [← subgroupOf_normalizer_eq hV]
    intro s hs
    have hm : (s : G) ∈ d.fixedSylow u ⊓ Lu := hS ▸ mem_map_of_mem Lu.subtype hs
    exact (show (T : Subgroup G) ≤ normalizer (V : Set G) by
      simpa only [F.last] using F.invariant 3) hm.1.1
  let Q : Sylow 2 Rudvalis.Model := S.mapSurjective r.onto
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Rudvalis.Model Q modelSylow
  have hmapS : (S : Subgroup Lu).map (r.align g).projection = localP := by
    change (S : Subgroup Lu).map ((MulAut.conj g).toMonoidHom.comp r.projection) = _
    rw [← map_map]
    change ((g • Q : Sylow 2 Rudvalis.Model) : Subgroup Rudvalis.Model) = _
    rw [hg]
    rfl
  let E := (V.subgroupOf Lu).map (r.align g).projection
  have hEP : E ≤ localP := hmapS ▸ map_mono hVS
  have hEn : localP ≤ normalizer (E : Set Rudvalis.Model) := by
    rw [← hmapS]
    exact (map_mono hSn).trans ((V.subgroupOf Lu).le_normalizer_map (r.align g).projection)
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hdisj := d.fixed_line_inf_seed_eq_bot earlier u hu hne (fun hc => hout (hLu.trans hc))
  have hcard : Nat.card E = 8 := by
    have hr : ((r.align g).seedProjection hV).range = E := by
      rw [FixedRudvalisCover.seedProjection, MonoidHom.range_comp, inclusion_range]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective
      ((r.align g).seedProjection_injective hV hdisj)).toEquiv]
    exact d.natural.seed_card
  exact ⟨g, RankOneEightCharacteristic.eq_elementary_two_of_normal_eight E hEP hEn hE hcard⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

include d in
/-- Generation by the original point residual places the original seed in O²(H). -/
theorem seed_le_residual_K : V ≤ K F := by
  have hLi : F.Li L 1 ≤ K F := by
    change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype ≤ _
    exact embedded_pResidual_mono 2 inf_le_right
  calc
    V = ⁅V, F.Li L 1⁆ := d.seed_eq_commutator_pointResidual
    _ ≤ ⁅F.U, K F⁆ := commutator_mono (V_le_U F) hLi
    _ ≤ K F := d.U_commutator_K_le

/-- The original eight in the recognized Ru cover. All ambient source hypotheses
are retained. The first conclusion supplies the independent L₁-complement
argument; the last uses only an inner change of the actual recognition map.
Neither seed containment nor its marked image is assumed. -/
theorem fixedRudvalis_originalEight
    (earlier : d.ModuleSeparation) (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hne : (u : G) ≠ 1) (_hfix : d.FixedModuloPoint u)
    (_hNK : normalizer (K F : Set G) = F.H) (_hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (_hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (_hq : Theory.GroupTheory.IsQuasisimple Lu)
    (r : d.FixedRudvalisCover u Lu) :
    V = ⁅V, F.Li L 1⁆ ∧ V ≤ Lu ∧
      ∃ g : Rudvalis.Model,
        (V.subgroupOf Lu).map (r.align g).projection = elementary 2 := by
  have hV := d.seed_le_residual_K.trans hKLu.le
  exact ⟨d.seed_eq_commutator_pointResidual, hV,
    marking_of_containment earlier hu hne hsyl hLu hn hout r hV⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
