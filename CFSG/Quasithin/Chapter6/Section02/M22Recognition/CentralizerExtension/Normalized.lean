module
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Centralizer geometry for the original normalized local subgroup

The outside involution construction needs the actual intersection T ∩ L to
be Sylow in L. Normalization by T gives this directly; no block classification
is needed for this geometric step. The marked conjugate eight then supplies
the involution and the existing centralizer argument gives its normal
sixteen and symmetric-four quotient.

The Chapter 6 hypothesis L normal in M, with T ≤ M, supplies this condition.
Source: Aschbacher–Smith, Proposition 6.2.13, printed pp.687–688.
-/
public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter6.Source
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]

private theorem exists_outside_involution_of_normalizes (T : Sylow 2 G) (L V U P : Subgroup G) (z d : G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hV : V = L.pCoreIn 2) (hnat : IsNaturalModule L V 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hUS : U ≤ (T : Subgroup G) ⊓ L)
    (hUV : U ⊓ V = V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G))
    (hZ : Nat.card (V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) : Subgroup G) = 4)
    (hUP : U ≤ P) (hdL : d ∈ L)
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G))
    (hd : orderOf d = 3)
    (hPP : P ⊓ P.map (MulAut.conj d⁻¹).toMonoidHom =
      V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)) :
    ∃ t : centralizer ({z} : Set G),
      t ∈ centralizer (U.subgroupOf (centralizer ({z} : Set G)) :
        Set (centralizer ({z} : Set G))) ∧
      t ∉ U.subgroupOf (centralizer ({z} : Set G)) ∧ t ^ 2 = 1 := by
  let S := (T : Subgroup G) ⊓ L
  let Z := V ⊓ centralizer (S : Set G)
  let f := (MulAut.conj d⁻¹).toMonoidHom
  let B := U.map f
  obtain ⟨S₀, hS₀⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hSmap : (S₀ : Subgroup L).map L.subtype = S := by
    rw [hS₀, subgroupOf_map_subtype]
  have hd3 : d ^ 3 = 1 := hd ▸ pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by
    intro h
    subst d
    simp at hd
  have hBC : B ≤ centralizer (U : Set G) :=
    NaturalInvolution.conjugate_eight_le_centralizer L V S U hV hnat S₀ hSmap hU hUS hUV hZ d hdL hdS hd3 hd1
  have hB : Nat.card B = 8 := (card_map_of_injective (MulAut.conj d⁻¹).injective).trans hU
  have hnot : ¬ B ≤ U := by
    intro h
    have hBZ : B ≤ Z := by
      have hPP' : P ⊓ P.map f = Z := hPP
      rw [← hPP']
      exact le_inf (h.trans hUP) (map_mono hUP)
    have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hBZ)
      (Subgroup.inclusion_injective hBZ)
    have hZ' : Nat.card Z = 4 := hZ
    rw [hB, hZ'] at hc
    omega
  obtain ⟨t, htB, htU⟩ := SetLike.not_le_iff_exists.mp hnot
  have hfS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer _).inv_mem hdS)
  have hBS : B ≤ S := hfS ▸ map_mono (f := f) hUS
  have htH : t ∈ centralizer ({z} : Set G) := hTH (hBS htB).1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  refine ⟨⟨t, htH⟩, ?_, htU,
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian t htB)⟩
  apply mem_centralizer_iff.mpr
  intro u hu
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hBC htB) (u : G) hu


/-- The local construction with the Sylow restriction supplied by normalization. -/
theorem source_centralizer_extension_of_normalizes
    (H M L V : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M)
    (hTH : (T : Subgroup G) ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hV : V = L.pCoreIn 2) (hnat : Source.IsNaturalModule L V 2)
    [(V.subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient (V.subgroupOf M) (L.subgroupOf M))
    (P S : Subgroup H) [P.Normal] (h : CoreData P) (ha : NaturalFourOrbit P S)
    [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hZS : coreCenter P ≤ S) (hSP : S ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hSdef : S.map H.subtype = V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G))
    (hbranch : (sourceEight S).map H.subtype ⊓ V = S.map H.subtype)
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G))
    (hd : orderOf d = 3)
    (hPP : P.map H.subtype ⊓
      (P.map H.subtype).map (MulAut.conj d⁻¹).toMonoidHom = S.map H.subtype) :
    (centralizer (sourceEight S : Set H)).Normal ∧
      IsElementaryAbelian 2 (centralizer (sourceEight S : Set H)) ∧
      Nat.card (centralizer (sourceEight S : Set H)) = 16 ∧
      Nonempty ((H ⧸ centralizer (sourceEight S : Set H)) ≃* Equiv.Perm (Fin 4)) := by
  subst H
  let H := centralizer ({z} : Set G)
  let A := sourceEight S
  let U := A.map H.subtype
  have hVL : V ≤ L := by
    rw [hV]
    exact map_subtype_le _
  have hVM : V ≤ M := hVL.trans hLM
  have hTmap : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map M.subtype = T := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]
  have hUloc := sourceEight_le_sylow_inf_layer H M P S h ha hS hZS hSP
    (T.subtype hTM) (V.subgroupOf M) (L.subgroupOf M) hq
    (hTmap.symm ▸ hTH) (hTmap.symm ▸ hPT)
    (by rwa [map_subgroupOf_eq_of_le hVM])
  have hUTL : U ≤ (T : Subgroup G) ⊓ L := by
    simpa only [map_inf _ _ M.subtype M.subtype_injective, hTmap,
      map_subgroupOf_eq_of_le hLM] using hUloc
  let : IsElementaryAbelian 2 A := sourceEight_elementary h ha hS
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map H.subtype
  have hA : Nat.card A = 8 := sourceEight_card h ha hZS
  have hU : Nat.card U = 8 := (card_map_of_injective H.subtype_injective).trans hA
  have hC : Nat.card (centralizer (A : Set H)) = 16 :=
    sourceEight_centralizer_card h ha hS hZS hSP
  have hUP : U ≤ P.map H.subtype := map_mono (sourceEight_le_core P S hSP)
  have hUV : U ⊓ V = V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) :=
    hbranch.trans hSdef
  have hZ : Nat.card (V ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) : Subgroup G) = 4 := by
    rw [← hSdef, card_map_of_injective H.subtype_injective, hS]
  obtain ⟨t, ht, htA, ht2⟩ := exists_outside_involution_of_normalizes
    T L V U (P.map H.subtype) z d hTL hV hnat hTH hU hUTL hUV hZ
    hUP hdL hdT hd (hPP.trans hSdef)
  have hUA : U.subgroupOf H = A :=
    comap_map_eq_self_of_injective H.subtype_injective A
  change t ∈ centralizer (U.subgroupOf H : Set H) at ht
  change t ∉ U.subgroupOf H at htA
  rw [hUA] at ht htA
  have hc := coreCenter_card h
  have : Nontrivial (coreCenter P) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne (1 : coreCenter P)
  let wA : A := ⟨w, sourceEight_contains S (hZS w.property)⟩
  have hwA : wA ≠ 1 := by
    intro he
    apply hw
    apply Subtype.ext
    exact congrArg (fun a : A => (a : H)) he
  exact ⟨inferInstance,
    elementary_centralizer_of_outside_involution A hA hC t ht htA ht2, hC,
    centralizer_quotient_symmetric_four A h.card hA hC wA hwA (h.center_le w.property)⟩

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
