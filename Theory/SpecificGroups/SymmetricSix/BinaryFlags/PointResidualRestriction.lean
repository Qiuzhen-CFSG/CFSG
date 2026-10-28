module
public import Theory.GroupTheory.PResidual.IndexThreeNormalized
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard

/-!
# Two-perfect images in natural A₆ point stabilizers

The residual of each natural-line stabilizer in a six-letter group containing
A₆ has order twelve. Its Sylow two-subgroups therefore have index three.
A two-perfect subgroup normalized by such a Sylow subgroup is either trivial
or the full residual. The final theorem retains the map from the source group,
so the conclusion applies to its actual image rather than an abstract model.

Source: Aschbacher–Smith, 13.3.9, printed p.887. This establishes the
natural-module image step; the ambient theta/TI and subgroup recovery arguments
are separate earlier source steps.
-/

public section
open Subgroup

private theorem index_three_of_residual_card {G:Type*} [Group G] [Finite G]
    (hc:Nat.card (pResidual 2 G)=12) (T:Sylow 2 G) : (T:Subgroup G).index=3 := by
  obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual 2 (G:=G)).exists_card_eq
  change (pResidual 2 G).index=2^n at hn
  have hg:Nat.card G=12*2^n := by
    rw [←(pResidual 2 G).card_mul_index,hc,hn]
  have hco:Nat.Coprime (T:Subgroup G).index (2^n) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr T.not_dvd_index).symm).pow_right n
  have hd:(T:Subgroup G).index∣12 :=
    hco.dvd_mul_right.mp (hg ▸ (T:Subgroup G).index_dvd_card)
  have hb:(T:Subgroup G).index≤12 := Nat.le_of_dvd (by decide) hd
  have hp:0<(T:Subgroup G).index := Nat.card_pos
  have he:(T:Subgroup G).index=1 ∨ (T:Subgroup G).index=3 := by
    have ho:=T.not_dvd_index
    have h5:(T:Subgroup G).index≠5 := by intro he;rw[he] at hd;norm_num at hd
    have h7:(T:Subgroup G).index≠7 := by intro he;rw[he] at hd;norm_num at hd
    have h9:(T:Subgroup G).index≠9 := by intro he;rw[he] at hd;norm_num at hd
    have h11:(T:Subgroup G).index≠11 := by intro he;rw[he] at hd;norm_num at hd
    omega
  rcases he with he|he
  · have ht:(T:Subgroup G)=⊤:=index_eq_one.mp he
    have hG:IsPGroup 2 G := (T.isPGroup'.of_equiv (MulEquiv.subgroupCongr ht)).of_equiv (Subgroup.topEquiv)
    have hr:=hG.to_subgroup (pResidual 2 G)
    obtain ⟨k,hk⟩:=hr.exists_card_eq
    rw[hc] at hk
    have hd3:3∣2^k := hk ▸ (by decide:3∣12)
    exact False.elim ((by decide:¬3∣2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd3))
  · exact he

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry BinaryPermutation Representation.BinaryOffender

theorem point_sylow_index_three (I:Subgroup S) (hI:alternatingGroup (Fin 6)≤I)
    (P:Submodule (ZMod 2) V) (hP:Module.finrank (ZMod 2) P=1)
    (T:Sylow 2 (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P : Subgroup S)) :
    (T:Subgroup (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P : Subgroup S)).index=3 := by
  apply index_three_of_residual_card
  have hh:=NaturalResidualCard.point_residual_card I hI P hP
  dsimp only at hh
  rw [card_map_of_injective (subtype_injective _)] at hh
  exact hh
/-- A Sylow-normalized two-perfect subgroup in the actual natural-line stabilizer
is trivial or is its full embedded two-residual. -/
theorem point_twoPerfect_normalized (I:Subgroup S) (hI:alternatingGroup (Fin 6)≤I)
    (P:Submodule (ZMod 2) V) (hP:Module.finrank (ZMod 2) P=1)
    (T:Sylow 2 (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P : Subgroup S))
    (N:Subgroup S) (hN:N≤I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P)
    (hp:IsPPerfect 2 N)
    (hn:(T:Subgroup (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P : Subgroup S)).map
      (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P).subtype≤normalizer (N:Set S)) :
    N=⊥ ∨ N=(pResidual 2 (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P : Subgroup S)).map
      (I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P).subtype := by
  let J:=I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P
  have hNJ:N≤J:=hN
  let N':=N.subgroupOf J
  have hp':IsPPerfect 2 N' := hp.of_surjective
    (subgroupOfEquivOfLe hN).symm.toMonoidHom (subgroupOfEquivOfLe hN).symm.surjective
  have hn':(T:Subgroup J)≤normalizer (N':Set J) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro n
    exact mem_normalizer_iff.mp (hn (mem_map_of_mem _ ht)) n.val
  rcases eq_bot_or_residual_of_index_three (T:Subgroup J) N' T.isPGroup'
    (point_sylow_index_three I hI P hP T) hp' hn' with hh|hh
  · left
    have he:=congrArg (Subgroup.map J.subtype) hh
    simpa only [N',map_subgroupOf_eq_of_le hNJ,Subgroup.map_bot] using he
  · right
    have he:=congrArg (Subgroup.map J.subtype) hh
    simpa only [N',map_subgroupOf_eq_of_le hNJ] using he
/-- The same conclusion for a genuine quotient image, retaining the map from
the original group and the image of its actual residual. -/
theorem point_image_twoPerfect {H:Type*} [Group H] [Finite H]
    (f:H→*S) (I:Subgroup S) (hI:alternatingGroup (Fin 6)≤I)
    (P:Submodule (ZMod 2) V) (hP:Module.finrank (ZMod 2) P=1)
    (hf:f.range=I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P)
    (T:Sylow 2 H) (N:Subgroup H) (hp:IsPPerfect 2 N)
    (hn:(T:Subgroup H)≤normalizer (N:Set H)) :
    N.map f=⊥ ∨ N.map f=(pResidual 2 H).map f := by
  let T':=T.mapSurjective f.rangeRestrict_surjective
  let N':=N.map f.rangeRestrict
  have hi:(T':Subgroup f.range).index=3 := by
    have hh:=point_sylow_index_three I hI P hP
    rw [←hf] at hh
    exact hh T'
  have hp':IsPPerfect 2 N' := hp.of_surjective
    (f.rangeRestrict.subgroupMap N) (f.rangeRestrict.subgroupMap_surjective N)
  have hn':(T':Subgroup f.range)≤normalizer (N':Set f.range) :=
    (map_mono hn).trans (le_normalizer_map f.rangeRestrict)
  rcases eq_bot_or_residual_of_index_three (T':Subgroup f.range) N' T'.isPGroup'
    hi hp' hn' with hh|hh
  · left
    have he:=congrArg (Subgroup.map f.range.subtype) hh
    simpa only [N',map_map,MonoidHom.subtype_comp_rangeRestrict,Subgroup.map_bot] using he
  · right
    have he:=congrArg (Subgroup.map f.range.subtype) hh
    rw [←map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective] at he
    simpa only [N',map_map,MonoidHom.subtype_comp_rangeRestrict] using he
end Theory.SpecificGroups.SymmetricSix.BinaryFlags
