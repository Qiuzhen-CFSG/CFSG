module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiLinearKernelIdentity
public import Theory.Representation.SL2.OddFixedSmallFactors

/-!
# The two-factor case of the literal third-kernel centralizer quotient

Put C = C_(Q_m)(G_m^(3)), W = G_m^(2), and E = C/W in the
nonbinary Suzuki branch. The same selected full-edge torus acts without
nonidentity fixed points on E. The actual quotient action is transported
through the original endpoint marking to SL₂(k). Odd-order averaging
preserves the vanishing fixed space on quotients; the minimum binary
SL₂ degree and |E| ≤ q⁴ therefore give two irreducible factors of order
q² for every proper nonzero invariant subspace of E.

The radius-two center span V_m^(2) is normalized by the actual endpoint,
contains W, and has image of order at least q³. Consequently that image
cannot be proper, so V_m^(2) = C. This supplies the generation by V_m^(2)
and the preimage of a constituent used in the next source step, including
the original completion inclusion. The full second kernel W and this
larger radius-two span remain distinct throughout.

All earlier natural-center, reciprocal-commutator and original field and
quotient markings remain explicit. This proves the constituent-order and
span-generation steps, not the assertion that E is irreducible. The
natural-action identification of the two hypothetical constituents and
the ensuing (5.17) contradiction still belong to the source assembly.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.189--190, immediately after C_E(K_m) = 1.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem large_invariant_subgroup_eq
    {X H : Type*} [Group X] [Group H]
    (A C W U : Subgroup X) [Finite C]
    (hUC : U ≤ C) (hWU : W ≤ U)
    (hW : (W.subgroupOf C).Normal)
    (hAC : A ≤ normalizer (C : Set X)) (hAU : A ≤ normalizer (U : Set X))
    (π : A →* H) (hπ : Function.Surjective π) :
    let _ := hW
    ∀ hCE : IsElementaryAbelian 2 (C ⧸ W.subgroupOf C),
    let _ := hCE
    ∀ ρ : H →* MulAut (C ⧸ W.subgroupOf C),
    (∀ a : A, ∀ c : C, ρ (π a) (QuotientGroup.mk c) =
      QuotientGroup.mk ⟨(a : X)*c*(a : X)⁻¹,
        (mem_normalizer_iff.mp (hAC a.property) c).mp c.property⟩) →
    ∀ q : ℕ, 1 ≤ q →
    (∀ J : Subrepresentation (FrattiniAction.ofAutomorphismHom ρ),
      J ≠ ⊥ → J ≠ ⊤ → Nat.card J.toSubmodule ≤ q) →
    q < W.relIndex U → U = C := by
  let _ := hW
  dsimp only
  intro hCE
  let _ := hCE
  intro ρ hρ q hq hsmall hlarge
  let E := C ⧸ W.subgroupOf C
  let f := QuotientGroup.mk' (W.subgroupOf C)
  let P := (U.subgroupOf C).map f
  let e : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  let J : Subrepresentation (FrattiniAction.ofAutomorphismHom ρ) := {
    toSubmodule := e P
    apply_mem_toSubmodule g v hv := by
      obtain ⟨a,rfl⟩ := hπ g
      change v.toMul ∈ P at hv
      obtain ⟨c,hc,he⟩ := hv
      change ρ (π a) v.toMul ∈ P
      rw [←he]
      change ρ (π a) (QuotientGroup.mk c) ∈ P
      rw [hρ]
      exact mem_map_of_mem f ((mem_normalizer_iff.mp (hAU a.property) c).mp hc) }
  have hc : Nat.card J.toSubmodule = W.relIndex U := by
    have he : Nat.card J.toSubmodule = Nat.card P := Nat.card_congr {
      toFun v := ⟨v.val.toMul,v.property⟩
      invFun v := ⟨Additive.ofMul v.val,v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [he]
    change Nat.card ((U.subgroupOf C).map f) = _
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hUC]
  have hJb : J ≠ ⊥ := by
    intro hb
    have hh : Nat.card J.toSubmodule = 1 := by
      rw [hb]
      change Nat.card (⊥ : Submodule (ZMod 2) (Additive E)) = 1
      exact Nat.card_unique
    omega
  have hJt : J = ⊤ := by
    by_contra ht
    have hh := hsmall J hJb ht
    omega
  have hP : P = ⊤ := by
    apply e.injective
    exact (congrArg Subrepresentation.toSubmodule hJt).trans e.map_top.symm
  have hU : U.subgroupOf C = ⊤ := by
    have hh := congrArg (Subgroup.comap f) hP
    change ((U.subgroupOf C).map f).comap f = _ at hh
    rw [comap_map_eq,comap_top,QuotientGroup.ker_mk',
      sup_eq_left.mpr (subgroupOf_mono C hWU)] at hh
    exact hh
  apply le_antisymm hUC
  intro u hu
  have hh : (⟨u,hu⟩ : C) ∈ U.subgroupOf C := hU ▸ mem_top _
  exact hh

/-- Every proper nonzero constituent of the original C/W has order q², as does its irreducible quotient. -/
theorem source_suzuki_centralizer_two_factors
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let A := star L S i
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
    ∃ hAC : A ≤ normalizer (C : Set (G₀ L S)),
    ∃ hW : (W.subgroupOf C).Normal,
      letI := hW
      let E := C ⧸ W.subgroupOf C
      Nat.card k ^ 3 ≤ Nat.card E ∧
      Nat.card E ≤ Nat.card k ^ (4 : ℕ) ∧
      ∃ hCE : IsElementaryAbelian 2 E,
        letI := hCE
        ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
          MulAut E,
          (∀ t : A, ∀ c : C,
            ρ ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) (QuotientGroup.mk' (W.subgroupOf C) c) =
              QuotientGroup.mk' (W.subgroupOf C) ⟨(t : G₀ L S)*c*(t : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (hAC t.property) c).mp c.property⟩) ∧
          let τ : Representation (ZMod 2) SL(2,k) (Additive E) :=
            FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
          ∀ U : Subrepresentation τ, U ≠ ⊥ → U ≠ ⊤ →
            Nat.card (U.toSubmodule : Type _) = Nat.card k ^ (2 : ℕ) ∧
            Nat.card (Additive E ⧸ U.toSubmodule) = Nat.card k ^ (2 : ℕ) ∧
            U.toRepresentation.IsIrreducible ∧ U.quotientRepresentation.IsIrreducible := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let B := stabilizer F (base F (!i)) ⊓ stabilizer F m
  let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective (inclusion
    (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  obtain ⟨K,hK,ho,hKx,hDne,hDo,hJH,hJsize,hAC,hW,hWC,hCE,ρ,hρ,hfixed⟩ :=
    source_suzuki_selected_torus_quotient_fixed h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  let _ := hCE
  let E := Additive (C ⧸ W.subgroupOf C)
  let τ := FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
  let D := K.map B.subtype ⊓ A
  let π : D →* SL(2,k) := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 A)).comp (inclusion (show D ≤ A from inf_le_right))))
  have hodd : Odd (Nat.card π.range) := hDo.of_dvd_nat (card_range_dvd π)
  have hf : fixedSpace τ π.range = ⊥ := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Additive.toMul.injective
    apply hfixed v.toMul
    intro d
    have hh := hv (⟨π d,⟨d,rfl⟩⟩ : π.range)
    change ρ (e.symm (π d)) v.toMul = v.toMul at hh
    have hi : inclusion (show D ≤ A from inf_le_right) d =
        (⟨(d : G₀ L S),d.property.2⟩ : A) := Subtype.ext (coe_inclusion _ _)
    simpa only [π,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,
      hi,QuotientGroup.mk'_apply] using hh
  have hNW := (source_suzuki_full_linear_second_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  obtain ⟨_,hN,_,_,hupper,_⟩ := source_suzuki_centralizer_second_action h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hu : Nat.card E ≤ Nat.card k ^ (4 : ℕ) := by
    change Nat.card (C ⧸ W.subgroupOf C) ≤ _
    simpa only [hNW] using hupper
  have hlo : Nat.card k ^ 3 ≤ Nat.card E :=
    (source_suzuki_centralizer_growth_and_fixed_kernel h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.1
  have hd : Module.finrank (ZMod 2) E ≤ 4*(2*n+1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hfield,←pow_mul] at hu
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hu
    omega
  refine ⟨hAC,hW,hlo,hu,hCE,ρ,hρ,?_⟩
  dsimp only
  intro U hU hUt
  obtain ⟨hdu,hdq,hi,hq⟩ := Representation.SL2.small_factors_of_odd_fixed_free τ π.range hodd hf
    (by omega : 2*n+1 ≠ 0) hfield hd U hU hUt
  refine ⟨?_,?_,hi,hq⟩
  · rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdu,hfield,←pow_mul]
    congr 1
    omega
  · rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdq,hfield,←pow_mul]
    congr 1
    omega

/-- The radius-two span fills the actual third-kernel centralizer, including in the original completion. -/
theorem source_suzuki_centralizer_eq_radius_two_span
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    C = V F m 2 ∧ C.map (G₀ L S).subtype = (V F m 2).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let A := star L S i
  let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
  let U := V F m 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective (inclusion
    (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  obtain ⟨hAC,hW,_,_,hCE,ρ,hρ,hfactors⟩ := source_suzuki_centralizer_two_factors
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  let _ := hCE
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hUC : U ≤ C := (source_suzuki_centralizer_growth_and_fixed_kernel h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).1
  have hWU : W ≤ U := (source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear).2.2.1
  have hAU : A ≤ normalizer (U : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_normalizes_V F m 2)
  let π := e.toMonoidHom.comp ((originalQuotient h i).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A)))
  have hπ : Function.Surjective π := e.surjective.comp
    ((originalQuotient h i).symm.surjective.comp (QuotientGroup.mk'_surjective _))
  have heq : U = C := large_invariant_subgroup_eq A C W U hUC hWU hW hAC hAU π hπ hCE
    (ρ.comp e.symm.toMonoidHom) (by
      intro a c
      simpa only [π,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,
        QuotientGroup.mk'_apply] using hρ a c)
    (Nat.card k ^ 2) (by have hh : 0 < Nat.card k := Nat.card_pos; exact Nat.succ_le_of_lt (by positivity))
    (fun J hJ hJt => (hfactors J hJ hJt).1.le)
    (source_suzuki_radius_two_span_growth h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.2.1
  exact ⟨heq.symm,congrArg (Subgroup.map (G₀ L S).subtype) heq.symm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
