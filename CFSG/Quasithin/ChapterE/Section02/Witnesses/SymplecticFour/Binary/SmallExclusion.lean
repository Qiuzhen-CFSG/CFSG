module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.SmallImage
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.InvolutionFive
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.SmallPrime

/-!
# Excluding the original binary symplectic small automizer

The small-action hypotheses force the original elementary image in H/J to
have order two. Its nontrivial element centralizes the prescribed Sylow.
Minimal parabolicity makes this involution inner in the A6 component, so it
inverts an actual element of order five. The original small quaternion pair
allows only prime three, yielding the contradiction.

Every quotient, component and actor comes from the original E.2.17 data.
Source: Aschbacher--Smith E.2.17, printed pp.229--230.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem source_binary_symplectic_small_automizer_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : Nonempty (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2))))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (_hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  obtain ⟨eK⟩ := hm
  have hcard := source_image_card_two T hP hs K hK hgen eK V hVT hvn hcore hout
    hfit U hTU hU f hf hk hD hratio
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  obtain ⟨hLs,hLa,hLn,hLT⟩ := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hstar := Structure.source_star_minimal_core_free T hP
  have hWT : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hTW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  let eL := eK.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  obtain ⟨v,hv,hv1,r,hr,hi⟩ := coreFree_exists_inverted_five S hstar.1 hstar.2 L hLa hLT eL
    W hWT hTW hcard
  have hp := Involution.source_prime_inverter_eq_three T hP V hVT hvn hcore hout hfit hV
    U hTU hU f hf hk hD hratio hcard (by decide : Nat.Prime 5) (by decide) v r hv hv1 hr hi
  omega
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
