module
public import Theory.GroupTheory.NormalizerAction.OmegaCenterCentralizer
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentData

/-!
# The ordinary-component centralizer comparison in 15.1.22

Let Y be the literal O^{3'}(M ∩ L) for the chosen Case-I component.
The normalizer of L in S normalizes M ∩ L and hence Y. In the exact
source quotient N_{G1}(L)/C_{G1}(L), a first omega center of order two
which is moved by Y forces C_S(Y) = C_S(L). The ordinary-component
commutation theorem supplies normalization of L by C_S(Y); no assumption
that S normalizes L is added.

The ordinary component identification, the model's omega-center order and
its residual-image noncentralization remain explicit source inputs. The
comparison itself, subgroup normalization, and transport to the original
ambient G are proved here.

Source: Aschbacher--Smith 15.1.22(**), printed p.1099.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup.NormalizerAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original centralizers in S agree after the two faithful-image
model facts have been supplied for the ordinary source component. -/
theorem source22_ordinary_residual_centralizer
    (d : CaseIComponentData T M Mc V) (hTM : (T : Subgroup G) ≤ M)
    (hL : IsComponentIn d.L d.G1)
    (hcard : Nat.card (omega₁ (center (sylowImage (d.L.subgroupOf d.G1)
      (d.S.subgroupOf d.G1))) (p := 2)) = 2)
    (hescape : let K := d.L.subgroupOf d.G1
      let A := sylowImage K (d.S.subgroupOf d.G1)
      let Y := (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype
      ¬ ((omega₁ (center A) (p := 2)).map (center A).subtype).map A.subtype ≤
        centralizer (((Y.subgroupOf d.G1).subgroupOf (normalizer (K : Set d.G1))).map
          (quotient K) : Set (NormalizerAction.Star K))) :
    let Y := (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype
    d.S ⊓ centralizer (Y : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  let C := M ⊓ d.L
  let Y := (primeToResidual 3 C).map C.subtype
  let K := d.L.subgroupOf d.G1
  let A := d.S.subgroupOf d.G1
  let B := Y.subgroupOf d.G1
  have hYL : Y ≤ d.L := (map_subtype_le _).trans inf_le_right
  have hNC : d.S ⊓ normalizer (d.L : Set G) ≤ normalizer (C : Set G) :=
    (le_inf ((inf_le_left.trans (d.S_le_T.trans hTM)).trans M.le_normalizer)
      inf_le_right).trans inf_normalizer_le_normalizer_inf
  have hNY : d.S ⊓ normalizer (d.L : Set G) ≤ normalizer (Y : Set G) :=
    hNC.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))
  have hn : A ⊓ normalizer (K : Set d.G1) ≤ normalizer (B : Set d.G1) := by
    rintro x ⟨hxA,hxK⟩
    have hxL : (x : G) ∈ normalizer (d.L : Set G) := by
      have hh := le_normalizer_map d.G1.subtype
        (mem_map_of_mem d.G1.subtype hxK)
      rwa [map_subgroupOf_eq_of_le hL.1] at hh
    exact le_normalizer_comap d.G1.subtype (hNY ⟨hxA,hxL⟩)
  have he := component_centralizer_eq_of_omega_center_escape K A B hL.2
    ((T.isPGroup'.to_le d.S_le_T).comap_of_injective d.G1.subtype d.G1.subtype_injective)
    hn (comap_mono hYL) hcard hescape
  have hm := congrArg (Subgroup.map d.G1.subtype) he
  rw [← map_inf_centralizer_of_injective d.G1.subtype d.G1.subtype_injective,
    ← map_inf_centralizer_of_injective d.G1.subtype d.G1.subtype_injective] at hm
  simpa only [A,B,K,map_subgroupOf_eq_of_le d.S_le_G1,
    map_subgroupOf_eq_of_le (hYL.trans hL.1),map_subgroupOf_eq_of_le hL.1] using hm
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
