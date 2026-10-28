module
public import Theory.Mathieu.M24.LargeElementaryPerfectNormalizer
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Radical-free sections of large elementary normalizers in M24

The native catalogue places an elementary subgroup of order64 in one of two
classes. Its normalizer is a trio or sextet stabilizer. The sextet order is
prime to seven. The trio has quotient S3 times L3(2), with two-group kernel.
After any solvable normal kernel is killed, a section therefore has order
at most168. It cannot be the full order336 nonsingular point action.

`MathieuComponent` applies this to the literal component central quotient
and local point-centralizer action in12.1.1. No Sylow-normality assumption
or new enumeration is needed here.
Source: Aschbacher--Smith12.1.1, printed p.788; H.14.1(1,5), pp.396--397;
GLS3 Table5.3e. Existing native model certificates retain their attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups PairOvergroups.QuotientConstruction

private theorem solvable_kernel_le {A Q : Type*} [Group A] [Group Q]
    (f : A →* Q) (hf : Function.Surjective f) (hr : solvableRadical Q = ⊥)
    (N : Subgroup A) [N.Normal] [Group.IsSolvable N] : N ≤ f.ker := by
  have hn := (inferInstance : N.Normal).map f hf
  have hs : Group.IsSolvable (N.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  have hh := le_solvableRadical (N.map f) hn hs
  rw [hr] at hh
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hh)

private theorem trio_radical_free_section_card {A Q : Type*} [Group A] [Finite A]
    [Group Q] [Finite Q] (i : A →* trioStabilizer standardTrio)
    (hi : Function.Injective i) (f : A →* Q) (hf : Function.Surjective f)
    (hr : solvableRadical Q = ⊥) : Nat.card Q ≤ 168 := by
  let q := (affineQuotient affineCoverage).comp i
  have hq : IsPGroup 2 q.ker :=
    (affineQuotient_kernel_isPGroup affineCoverage).comap_of_injective i hi
  let : Group.IsNilpotent q.ker := hq.isNilpotent
  let l := (MonoidHom.snd (Equiv.Perm (Fin 3)) SL(3,ZMod 2)).comp q
  let N := (MonoidHom.snd (Equiv.Perm (Fin 3)) SL(3,ZMod 2)).ker
  let c : N →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst (Equiv.Perm (Fin 3)) SL(3,ZMod 2)).comp N.subtype
  have hc : Function.Injective c := by
    intro a b he
    apply Subtype.ext
    exact Prod.ext he (a.property.trans b.property.symm)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hc
  let : Group.IsSolvable l.ker := isSolvable_comap_of_solvable_ker q N
  have hk := solvable_kernel_le f hf hr l.ker
  let g : l.range →* Q := l.rangeRestrict.liftOfSurjective l.rangeRestrict_surjective
    ⟨f,by simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have hg (a : A) : g (l.rangeRestrict a) = f a :=
    l.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ a
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨a,rfl⟩ := hf y
    exact ⟨l.rangeRestrict a,hg a⟩
  have hb := (Nat.card_le_card_of_surjective g hgs).trans
    (Nat.card_le_card_of_injective l.range.subtype l.range.subtype_injective)
  simpa only [Matrix.PSL3Two.card_SL] using hb

/-- A radical-free quotient of a subgroup normalizing an elementary sixty-four
in M24 cannot have order336. -/
theorem mathieu_no_full_three_action {A Q : Type*} [Group A] [Finite A]
    [Group Q] [Finite Q] (i : A →* M24) (hi : Function.Injective i)
    (E : Subgroup M24) [IsElementaryAbelian 2 E] (hE : Nat.card E = 64)
    (hn : i.range ≤ normalizer (E : Set M24))
    (f : A →* Q) (hf : Function.Surjective f) (hr : solvableRadical Q = ⊥)
    (hc : Nat.card Q = 336) : False := by
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  let a := MulAut.conj g
  let U := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
  have hUP : U ≤ SylowNormalizer.candidate := by
    have h := map_mono (f := a.toMonoidHom) hES
    change U ≤ (g • S : Sylow 2 M24) at h
    rw [hg] at h
    exact h
  have hU : Nat.card U = 64 := by rwa [card_map_of_injective a.injective]
  have hcases := M24ChapterHStabilizers.ElementaryFusion.elementary_card64_eq_candidate U hU hUP
  have hN : (a.toMonoidHom.comp i).range ≤ normalizer (U : Set M24) := by
    rw [MonoidHom.range_comp]
    exact (map_mono hn).trans (le_normalizer_map a.toMonoidHom)
  have hrow (k : Fin 2) (hk : U = EvenCandidates.elementary k) : False := by
    let j : A →* EvenCandidates.localGroup k := (a.toMonoidHom.comp i).codRestrict _
      (fun x => by change _ ∈ normalizer (EvenCandidates.elementary k : Set M24); rw [←hk]; exact hN ⟨x,rfl⟩)
    have hj : Function.Injective j := fun x y h => hi (a.injective (congrArg Subtype.val h))
    fin_cases k
    · have hb := trio_radical_free_section_card
        (EvenCatalogue.NormalSeeds.trioNormalizerEquiv.toMonoidHom.comp j)
        (EvenCatalogue.NormalSeeds.trioNormalizerEquiv.injective.comp hj) f hf hr
      omega
    · have hd : 7 ∣ Nat.card Q := by rw [hc]; decide
      have hA := hd.trans (card_dvd_of_surjective f hf)
      have hS := hA.trans (card_dvd_of_injective
        (EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toMonoidHom.comp j)
        (EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.injective.comp hj))
      rw [SextetCore.stabilizer_card] at hS
      norm_num at hS
  exact hcases.elim (hrow 0) (hrow 1)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
