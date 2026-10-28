module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.DiagonalCentralizer

/-!
# The common-line odd core is an ambient Sylow subgroup

Assume the two marked cubic odd cores D and E have order 27, and put
K=D∩E. The literal odd core P of C_G(K) contains D and E: both are odd
subgroups of this centralizer, whose odd core has index two. Since D and
E are self-centralizing, C_G(P)=K; as K≤P, also Z(P)=K.

The normalizers of P and K coincide. The original Klein four torus acts
nontrivially on K, since its centralizer has order prime to three. Thus
|N_G(K):C_G(K)|=2 and |N_G(P):P|=4. Normalizer control promotes P to an
ambient Sylow three-subgroup. Its full normalizer is P times the original
torus, with trivial intersection. The preceding centralizer-order bounds
now give ambient Sylow order 243 or 729, excluding 3^7 from |G| in this
branch.

These are consequences of the actual (G1)–(G2) configuration of
Aschbacher–Smith I.4.5, printed p.417. They continue the exceptional q=3
analysis without the q>3 line-selection step in Fong, Nagoya Math. J.39
(1970), §6C, pp.75–77. The two remaining Sylow orders, the Sylow-nine
branch and the Atlas recognition equivalence are not excluded here.
`Chapter14DiagonalSylow` supplies the original SourceLocalData application,
discharging the Sylow and full-normalizer premises in this branch.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

def commonLineCore (t : CubicTorus c) : Subgroup G :=
  let C := Subgroup.centralizer
    ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
  (pPrimeCore 2 C).map C.subtype

private theorem commonLineCore_contains (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    cubicOddCore c t.x ≤ t.commonLineCore ∧
      cubicOddCore (swapFactors c) t.y ≤ t.commonLineCore := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let C := Subgroup.centralizer ((D⊓E:Subgroup G):Set G)
  let O := pPrimeCore 2 C
  have hi : O.index=2 := (t.core_intersection_oddCore_index hc).1
  have hle (A : Subgroup G) (hAC : A≤C) (hA : Nat.card A=27) :
      A≤O.map C.subtype := by
    have hcard : Nat.card (A.subgroupOf C)=27 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hA
    have hr : O.relIndex (A.subgroupOf C)=1 := Nat.eq_one_of_dvd_coprimes
      (show Nat.Coprime O.index (Nat.card (A.subgroupOf C)) by rw [hi,hcard]; decide)
      (O.relIndex_dvd_index_of_normal _) (relIndex_dvd_card _ _)
    have hh := map_mono (f:=C.subtype) (relIndex_eq_one.mp hr)
    rwa [map_subgroupOf_eq_of_le hAC] at hh
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  have he : Nat.card E=27 := t.right_oddCore_twentySeven_of_left hc
  let : IsElementaryAbelian 3 E := t.right_oddCore_twentySeven_elementary he
  exact ⟨hle D (D.le_centralizer.trans (centralizer_le inf_le_left)) hc,
    hle E (E.le_centralizer.trans (centralizer_le inf_le_right)) he⟩

theorem commonLineCore_centralizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Subgroup.centralizer (t.commonLineCore:Set G)=
      cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  obtain ⟨hD,hE⟩ := t.commonLineCore_contains hc
  apply le_antisymm
  · have hleft := centralizer_le hD
    have hright := centralizer_le hE
    rw [t.left_oddCore_twentySeven_selfCentralizing hc] at hleft
    rw [t.right_oddCore_twentySeven_selfCentralizing
      (t.right_oddCore_twentySeven_of_left hc)] at hright
    exact le_inf hleft hright
  · apply le_centralizer_iff.mpr
    exact map_subtype_le _

theorem commonLineCore_center (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    centerIn t.commonLineCore=cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  change t.commonLineCore ⊓ Subgroup.centralizer (t.commonLineCore:Set G)=_
  rw [t.commonLineCore_centralizer hc]
  exact inf_eq_right.mpr (inf_le_left.trans (t.commonLineCore_contains hc).1)

theorem commonLineCore_isThreeGroup (t : CubicTorus c) : IsPGroup 3 t.commonLineCore := by
  apply IsPGroup.of_card_dvd_pow (n:=6)
  change Nat.card ((pPrimeCore 2 _).map _ ) ∣ 3^6
  rw [card_map_of_injective (Subgroup.subtype_injective _)]
  exact t.core_intersection_oddCore_card_dvd

theorem commonLineCore_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    normalizer (t.commonLineCore:Set G)=normalizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G) := by
  apply le_antisymm
  · have hh := normalizer_le_normalizer_centralizer t.commonLineCore
    rwa [t.commonLineCore_centralizer hc] at hh
  · exact (normalizer_le_normalizer_centralizer _).trans
      (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))

theorem core_intersection_centralizer_normalizer_index (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
    (Subgroup.centralizer (K:Set G)).relIndex (normalizer (K:Set G))=2 := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let C := Subgroup.centralizer (K:Set G)
  let N := normalizer (K:Set G)
  let : IsCyclic K := isCyclic_of_prime_card (t.oddCore_intersection_card_of_twentySeven hc)
  have hAut : Nat.card (MulAut K)=2 := by
    rw [IsCyclic.card_mulAut,t.oddCore_intersection_card_of_twentySeven hc]
    decide
  have hindex : C.relIndex N ∣ 2 := by
    have hh := card_dvd_of_injective _
      (QuotientGroup.kerLift_injective K.normalizerMonoidHom)
    rw [normalizerMonoidHom_ker,←index,←relIndex,hAut] at hh
    exact hh
  apply ((Nat.dvd_prime Nat.prime_two).mp hindex).resolve_left
  intro he
  have hNC : N≤C := relIndex_eq_one.mp he
  have hKA : K≤Subgroup.centralizer (t.torus.map c.H.subtype:Set G) :=
    le_centralizer_iff.mpr (t.torus_normalizes_core_intersection.trans hNC)
  apply t.three_not_dvd_torus_centralizer
  have hd := card_dvd_of_le hKA
  rwa [t.oddCore_intersection_card_of_twentySeven hc] at hd

private theorem commonLineCore_relative_index (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    t.commonLineCore.relIndex (normalizer (t.commonLineCore:Set G))=4 := by
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let C := Subgroup.centralizer (K:Set G)
  let N := normalizer (K:Set G)
  have hPC : t.commonLineCore≤C := map_subtype_le _
  have hCN : C≤N := Subgroup.centralizer_le_normalizer _
  have hrel : t.commonLineCore.relIndex C=2 := by
    change ((pPrimeCore 2 C).map C.subtype).relIndex C=2
    rw [relIndex,subgroupOf,comap_map_eq_self_of_injective C.subtype_injective]
    exact (t.core_intersection_oddCore_index hc).1
  rw [t.commonLineCore_normalizer hc]
  change t.commonLineCore.relIndex N=4
  rw [←relIndex_mul_relIndex t.commonLineCore C N hPC hCN,hrel,
    t.core_intersection_centralizer_normalizer_index hc]

theorem commonLineCore_sylow (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    ∃ P : Sylow 3 G, (P:Subgroup G)=t.commonLineCore := by
  let P := t.commonLineCore
  have hlocal : ¬3∣P.relIndex (normalizer (P:Set G)) := by
    rw [t.commonLineCore_relative_index hc]
    decide
  have hi := not_dvd_relIndex_of_normalizer_inf_le P (normalizer (P:Set G)) ⊤
    t.commonLineCore_isThreeGroup le_top hlocal inf_le_left
  have hi' : ¬3∣P.index := by simpa only [relIndex_top_right] using hi
  exact ⟨t.commonLineCore_isThreeGroup.toSylow hi',rfl⟩

theorem commonLineCore_normalizer_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (normalizer (t.commonLineCore:Set G))=Nat.card t.commonLineCore*4 := by
  have hh := relIndex_mul_relIndex (⊥:Subgroup G) t.commonLineCore
    (normalizer (t.commonLineCore:Set G)) bot_le le_normalizer
  rw [relIndex_bot_left,relIndex_bot_left,t.commonLineCore_relative_index hc] at hh
  exact hh.symm

theorem commonLineCore_normalizer_split (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    normalizer (t.commonLineCore:Set G)=t.commonLineCore ⊔ t.torus.map c.H.subtype ∧
      Disjoint t.commonLineCore (t.torus.map c.H.subtype) := by
  let P := t.commonLineCore
  let A := t.torus.map c.H.subtype
  let : IsKleinFour A := t.ambient_torus_kleinFour
  have hA : Nat.card A=4 := IsKleinFour.card_four
  have hAN : A≤normalizer (P:Set G) := by
    rw [t.commonLineCore_normalizer hc]
    exact t.torus_normalizes_core_intersection
  have hp : Nat.card P∣3^6 := by
    change Nat.card ((pPrimeCore 2 _).map _)∣3^6
    rw [card_map_of_injective (Subgroup.subtype_injective _)]
    exact t.core_intersection_oddCore_card_dvd
  have hd : Disjoint P A := disjoint_of_coprime_natCard (by
    rw [hA]
    exact (by decide : Nat.Coprime (3^6) 4).of_dvd_left hp)
  refine ⟨?_,hd⟩
  apply Eq.symm
  apply eq_of_le_of_card_ge (sup_le le_normalizer hAN)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint P A hAN hd,hA,
    t.commonLineCore_normalizer_card hc]

theorem sylow_three_card_of_twentySeven (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (P : Sylow 3 G) :
    Nat.card P=243 ∨ Nat.card P=729 := by
  obtain ⟨Q,hQ⟩ := t.commonLineCore_sylow hc
  have he : Nat.card P=Nat.card t.commonLineCore :=
    (Nat.card_congr (P.equiv Q).toEquiv).trans
      (congrArg (fun A : Subgroup G => Nat.card A) hQ)
  rw [he]
  change Nat.card ((pPrimeCore 2 _).map _)=243 ∨ Nat.card ((pPrimeCore 2 _).map _)=729
  rw [card_map_of_injective (Subgroup.subtype_injective _)]
  exact (t.core_intersection_centralizer_orders hc).1

theorem seventh_power_not_dvd_of_twentySeven (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) : ¬3^7∣Nat.card G := by
  intro hd
  let P : Sylow 3 G := default
  have hh := P.pow_dvd_card_of_pow_dvd_card hd
  rcases t.sylow_three_card_of_twentySeven hc P with he|he <;> rw [he] at hh <;> norm_num at hh

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
