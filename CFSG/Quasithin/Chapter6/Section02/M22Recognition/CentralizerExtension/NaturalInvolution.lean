module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.NaturalInvolution.Norm
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# An outside involution from the natural L₂(4) extension

This is the independent geometric implication needed in the `C_R(K) = Z`
branch of Aschbacher–Smith, Proposition 6.2.13, printed pp.687–688
(PDF pp.704–705) of `refs/quasithin.pdf`. It constructs an involution outside
the given elementary eight in its centralizer inside the actual `H = C_G(z)`.
It does not assemble the eight or the global recognition theorem.

Here `V` is the actual natural layer, equal to `O₂(L)`, and
`Z_S = C_V(T ∩ L)`. In the original parameterization of `Source.ZS`, use
`V = Source.layer L W`; its defining intersection is then exactly the one
in these statements. The source establishes the block on p.687 and the
order-three marked intersection `P ∩ P^d = Z_S` on p.688. All conjugates
use the source convention `x^d = d⁻¹ * x * d`.

The genuine Chapter C block supplies the Sylow restriction to `L` through
its subnormality in `M`. The natural-module norm calculation shows that
an involution `x` in this Sylow subgroup commutes with `x^d`. Since
`U = Z_S⟨x⟩`, the whole conjugate eight centralizes `U`. Its containment
in `T ∩ L` places it inside `H`, and the marked intersection prevents its
containment in `U`. Choosing an element of the difference gives the witness.

The source's elementary-eight and central-four facts are explicit inputs.
The other ambient extension data specialize this implication without any
splitting hypothesis for `M/V` or `H/P`.
-/

open Subgroup
open CFSG.Quasithin.Chapter6.Source

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension.NaturalInvolution

variable {G : Type*} [Group G] [Finite G]

private theorem sylow_of_block (T : Sylow 2 G) (L M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M)
    (hblock : CFSG.Quasithin.ChapterC.IsBlock (L.subgroupOf M)) :
    ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
  obtain ⟨S₀, hS₀⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_subnormal
    (L.subgroupOf M) hblock.subnormal
  let e := subgroupOfEquivOfLe hLM
  let S := S₀.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S, ?_⟩
  change ((S₀ : Subgroup (L.subgroupOf M)).map e.toMonoidHom).map L.subtype = _
  rw [hS₀]
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨ha, a.property⟩
  · intro hx
    exact ⟨⟨x, hx.2⟩, ⟨⟨⟨x, hLM hx.2⟩, hx.2⟩, hx.1, rfl⟩, rfl⟩

/-- The central four and the order-three norm force the whole conjugate
elementary eight to centralize the original eight. -/
public theorem conjugate_eight_le_centralizer (L V S U : Subgroup G)
    (hV : V = L.pCoreIn 2) (hnat : IsNaturalModule L V 2)
    (S₀ : Sylow 2 L) (hS₀ : (S₀ : Subgroup L).map L.subtype = S)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUS : U ≤ S)
    (hUV : U ⊓ V = V ⊓ centralizer (S : Set G))
    (hZ : Nat.card (V ⊓ centralizer (S : Set G) : Subgroup G) = 4)
    (d : G) (hdL : d ∈ L) (hdS : d ∈ normalizer (S : Set G))
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    U.map (MulAut.conj d⁻¹).toMonoidHom ≤ centralizer (U : Set G) := by
  let Z := V ⊓ centralizer (S : Set G)
  let f := (MulAut.conj d⁻¹).toMonoidHom
  have hZU : Z ≤ U := by
    change V ⊓ centralizer (S : Set G) ≤ U
    rw [← hUV]
    exact inf_le_left
  have hZC : Z ≤ centralizer (S : Set G) := inf_le_right
  have hSC : S ≤ centralizer (Z : Set G) := le_centralizer_iff.mp hZC
  have hfS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer _).inv_mem hdS)
  have hnormV : L ≤ normalizer (V : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnat
    exact hm.normalizes
  have hfV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer _).inv_mem (hnormV hdL))
  have hfZ : Z.map f ≤ Z := by
    change (V ⊓ centralizer (S : Set G)).map f ≤ V ⊓ centralizer (S : Set G)
    rw [map_inf _ _ f (MulAut.conj d⁻¹).injective, hfV]
    apply inf_le_inf_left
    have hh := map_centralizer_le_centralizer_image (S : Set G) f
    change (centralizer (S : Set G)).map f ≤ centralizer (S.map f : Set G) at hh
    rwa [hfS] at hh
  have hnot : ¬ U ≤ V := by
    intro h
    have he : U = Z := by simpa only [inf_eq_left.mpr h] using hUV
    have hc : Nat.card U = 4 := he ▸ hZ
    omega
  obtain ⟨x, hx, hxV⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxZ : x ∉ Z := fun h => hxV h.1
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hgen : Z ⊔ zpowers x = U := by
    apply eq_of_le_of_card_ge (sup_le hZU (zpowers_le.mpr hx))
    rw [card_sup_zpowers_of_normalizing_involution Z x hx2 hxZ
      (centralizer_le_normalizer _ (hSC (hUS hx))), hZ, hU]
  have hSL : S ≤ L := by
    rw [← hS₀]
    exact map_subtype_le _
  let x₀ : L := ⟨x, hSL (hUS hx)⟩
  let d₀ : L := ⟨d, hdL⟩
  have hx₀ : x₀ ∈ S₀ := by
    have : x ∈ (S₀ : Subgroup L).map L.subtype := hS₀ ▸ hUS hx
    obtain ⟨y, hy, he⟩ := this
    exact (show y = x₀ from Subtype.ext he) ▸ hy
  have hd₀ : d₀ ∈ normalizer (S₀ : Set L) := by
    apply mem_normalizer_iff.mpr
    intro a
    have ha : a ∈ S₀ ↔ (a : G) ∈ S := by
      rw [← hS₀]
      exact (mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
    have hb : d₀ * a * d₀⁻¹ ∈ S₀ ↔ ((d₀ * a * d₀⁻¹ : L) : G) ∈ S := by
      rw [← hS₀]
      exact (mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
    change a ∈ S₀ ↔ d₀ * a * d₀⁻¹ ∈ S₀
    rw [ha, hb]
    exact mem_normalizer_iff.mp hdS (a : G)
  have hc : Commute x (f x) := by
    have hh := involution_commutes_marked_conjugate L V hV hnat S₀ x₀ d₀ hx₀
      (Subtype.ext hx2) hd₀ (Subtype.ext hd3)
      (fun h => hd1 (congrArg Subtype.val h))
    change x * f x = f x * x
    simpa [f, x₀, d₀] using congrArg (fun a : L => (a : G)) hh.eq
  have hfxS : f x ∈ S := hfS ▸ mem_map.mpr ⟨x, hUS hx, rfl⟩
  have hfxC : f x ∈ centralizer (U : Set G) := by
    apply (le_centralizer_iff.mp ?_ : zpowers (f x) ≤ centralizer (U : Set G))
      (mem_zpowers _)
    rw [← hgen]
    apply sup_le
    · exact le_centralizer_iff.mp (zpowers_le.mpr (hSC hfxS))
    · exact le_centralizer_iff.mp (zpowers_le.mpr (by
        rw [mem_centralizer_iff]
        intro a ha
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
        exact (hc.zpow_left n).eq))
  calc
    _ = Z.map f ⊔ zpowers (f x) := by
      rw [← hgen, Subgroup.map_sup, MonoidHom.map_zpowers]
    _ ≤ centralizer (U : Set G) :=
      sup_le (hfZ.trans (hZC.trans (centralizer_le hUS))) (zpowers_le.mpr hfxC)

/-- The marked intersection supplies an actual involution in `C_H(U) \ U`,
where `H = C_G(z)`. The eight and its intersection with the natural layer are
explicit hypotheses, to be supplied by the source-eight construction. -/
public theorem exists_outside_involution (T : Sylow 2 G) (L M V U P : Subgroup G) (z d : G)
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M)
    (hblock : CFSG.Quasithin.ChapterC.IsBlock (L.subgroupOf M))
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
  obtain ⟨S₀, hS₀⟩ := sylow_of_block T L M hTM hLM hblock
  have hd3 : d ^ 3 = 1 := hd ▸ pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by
    intro h
    subst d
    simp at hd
  have hBC : B ≤ centralizer (U : Set G) :=
    conjugate_eight_le_centralizer L V S U hV hnat S₀ hS₀ hU hUS hUV hZ d hdL hdS hd3 hd1
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

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension.NaturalInvolution
