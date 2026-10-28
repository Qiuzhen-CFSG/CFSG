module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Residual
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.QuotientModel.Source
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Quotients
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalizer placement of the corrected orthogonal residual

The lift maps modulo U to the selected involution line. Its normalizer
therefore centralizes that involution image. The selected diagonal image is
the intersection of the normal component square with this centralizer, so
its full inverse image K₀U is invariant. Its solvable residual is invariant
as well, giving the corrected local C-component in the original Sylow
normalizer. The two-core remains nontrivial because it contains the original
lift D.

Source: Aschbacher–Smith, Lemma 14.4.9, final paragraph, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- The involution-line image and normal-square intersection force normalization
of the full inverse image of the diagonal. -/
theorem normalizes_actor_of_fixed_image
    {X Q : Type*} [Group X] [Group Q] [Finite Q] (f : X →* Q)
    (K D S : Subgroup X) (J : Subgroup Q) [J.Normal] (i : X)
    (horder : orderOf (f i) = 2)
    (hD : D.map f = zpowers (f i)) (hS : S ≤ normalizer (D : Set X))
    (hK : K.map f = J ⊓ centralizer ({f i} : Set Q)) :
    S ≤ normalizer (K ⊔ f.ker : Subgroup X) := by
  have hSc : S.map f ≤ centralizer ({f i} : Set Q) := by
    have hn := (map_mono hS).trans (le_normalizer_map f)
    rw [hD, normalizer_zpowers_eq_centralizer_of_order_two _ horder] at hn
    exact hn
  have hSK : S.map f ≤ normalizer (K.map f : Set Q) := by
    rw [hK]
    apply (le_inf (show S.map f ≤ normalizer (J : Set Q) from le_normalizer_of_normal)
      (hSc.trans (centralizer ({f i} : Set Q)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hn := map_le_iff_le_comap.mp hSK
  rw [comap_normalizer_eq_of_le_range (map_le_range f K), comap_map_eq] at hn
  exact hn

/-- The original source selection gives the required fixed-image equality;
only the literal involution-line image is needed from the lift calculation. -/
theorem selected_normalizes_actor
    {X : Type*} [Group X] [Finite X] (K D S : Subgroup X) (i : X)
    (d : QuotientModel.SelectedComponentData (X ⧸ pCore 2 X)
      (QuotientGroup.mk' (pCore 2 X) i) (K.map (QuotientGroup.mk' (pCore 2 X))))
    (hi : orderOf (QuotientGroup.mk' (pCore 2 X) i) = 2)
    (hD : D.map (QuotientGroup.mk' (pCore 2 X)) =
      zpowers (QuotientGroup.mk' (pCore 2 X) i))
    (hS : S ≤ normalizer (D : Set X)) :
    S ≤ normalizer (K ⊔ pCore 2 X : Subgroup X) := by
  let _ := d.normal
  simpa only [QuotientGroup.ker_mk'] using
    normalizes_actor_of_fixed_image (QuotientGroup.mk' (pCore 2 X)) K D S
      d.square i hi hD hS d.fixed

/-- The literal lift and selected fixed component force normalization of K₀U.
The involution image and its exact order are deduced here, so this applies
in particular to the original T_D without an additional placement premise. -/
theorem source_normalizes_actor
    (U S : Subgroup G) (z i : G) (hi : orderOf i = 2)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hzU : zpowers z ≤ U) (hiz : i ∈ centralizer ({z} : Set G)) (hout : i ∉ U)
    (hSH : S ≤ centralizer ({z} : Set G))
    (hSD : S ≤ normalizer (centralizerLift U z i : Set G))
    (d : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    S ≤ normalizer (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  let K := diagonalResidual H i
  let D := centralizerLift U z i
  let iH : H := ⟨i,hiz⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hUH : U ≤ H := hUcore ▸ pCoreIn_le 2 H
  have hKH : K ≤ H := (map_subtype_le _).trans inf_le_left
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hUcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hiU := hHU hiz
  have hB : ⁅U,zpowers i⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  have hDle : D ≤ U ⊔ zpowers i :=
    sup_le (sup_le (hB.trans le_sup_left) le_sup_right) (hzU.trans le_sup_left)
  have hDH : D ≤ H := hDle.trans (sup_le hUH (zpowers_le.mpr hiz))
  have hUintr : U.subgroupOf H = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hUH]
    exact hUcore.symm
  have hDmap : (D.subgroupOf H).map q = zpowers (q iH) := by
    apply le_antisymm
    · have hh := map_mono (f := q) (subgroupOf_mono H hDle)
      rw [subgroupOf_sup hUH (zpowers_le.mpr hiz), Subgroup.map_sup, hUintr] at hh
      have hk : (pCore 2 H).map q = ⊥ := by
        apply (Subgroup.map_eq_bot_iff _).mpr
        rw [QuotientGroup.ker_mk']
      have he : (zpowers i).subgroupOf H = zpowers iH := by
        apply map_injective H.subtype_injective
        rw [map_subgroupOf_eq_of_le (zpowers_le.mpr hiz), MonoidHom.map_zpowers]
        rfl
      simpa only [hk, he, MonoidHom.map_zpowers, bot_sup_eq] using hh
    · apply zpowers_le.mpr
      exact mem_map_of_mem q
        ((show zpowers i ≤ D from le_sup_right.trans le_sup_left) (mem_zpowers i))
  have hqi : orderOf (q iH) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hiH : iH ^ 2 = 1 := Subtype.ext (by rw [← hi]; exact pow_orderOf_eq_one i)
      rw [hiH,map_one]
    · intro he
      have hc : iH ∈ pCore 2 H := (QuotientGroup.eq_one_iff _).mp he
      exact hout (hUcore ▸ mem_map_of_mem H.subtype hc)
  have hn := selected_normalizes_actor (K.subgroupOf H) (D.subgroupOf H)
    (S.subgroupOf H) iH d hqi hDmap (by
      rw [← subgroupOf_normalizer_eq hDH]
      exact subgroupOf_mono H hSD)
  rw [← hUintr, ← subgroupOf_sup hKH hUH,
    ← subgroupOf_normalizer_eq (sup_le hKH hUH)] at hn
  intro a ha
  exact hn (show (⟨a,hSH ha⟩ : H) ∈ S.subgroupOf H from ha)

/-- A C-component residual normalized by the actual Sylow subgroup belongs
to its local family. The nontrivial normal two-subgroup supplies the two-core
clause; neither local-family membership nor a core equality is an input. -/
theorem residual_mem_localFamily
    (A D S N : Subgroup G) (hAN : A ≤ N) (hS : Chapter1.IsSylowIn 2 S N)
    (hSA : S ≤ normalizer (A : Set G))
    (hres : (solvableResidual A).IsCComponent)
    (hD : IsPGroup 2 D) (hne : D ≠ ⊥) (hDS : D ≤ S)
    (hAD : A ≤ normalizer (D : Set G)) (hSD : S ≤ normalizer (D : Set G)) :
    (solvableResidual A).map A.subtype ∈ Chapter1.L G S := by
  let H := A ⊔ S
  let A' := A.subgroupOf H
  let e : A' ≃* A := subgroupOfEquivOfLe le_sup_left
  have hc := hres.map_equiv e.symm
  rw [map_solvableResidual_eq e.symm.toMonoidHom e.symm.surjective] at hc
  have hn : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hSA)
  have hcomp := hc.map_subtype hn.isSubnormal
  have hmap : (solvableResidual A').map A'.subtype =
      ((solvableResidual A).map A.subtype).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans le_sup_left), map_map]
    rw [← map_solvableResidual_eq e.toMonoidHom e.surjective, map_map]
    rfl
  rw [hmap] at hcomp
  have hcore : D ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hD (hDS.trans le_sup_right) (sup_le hAD hSD)
  have hSH : Chapter1.IsSylowIn 2 S H :=
    hS.restrict le_sup_right (sup_le hAN (Chapter1.isSylowIn_iff.mp hS).2.1)
  exact Chapter1.mem_L_of_cComponent
    (fun he => hne (bot_unique (he ▸ hcore))) hSH
    ((map_subtype_le _).trans le_sup_left) hcomp

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
