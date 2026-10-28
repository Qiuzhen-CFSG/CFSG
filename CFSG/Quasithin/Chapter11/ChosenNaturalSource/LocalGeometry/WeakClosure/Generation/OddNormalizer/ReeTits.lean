module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OrdinaryModels
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Rank
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding

/-!
# Ree and Tits exclusions for the original nonbinary covering pair

The full Ree parabolic projections retain their complementary tori and
have two-group kernels. A perfect actor kills the torus character, so its
odd Sylow subgroups embed in SL₂ or Suzuki groups and are cyclic. The
actual Tits embedding transfers this bound to its two-local normalizers.
The literal C.2.8 quotient preserves the original odd-rank-two witness,
excluding both families in the ordinary component branch.

The endpoint applies these exclusions to the same Hall kernel. Remaining
sporadic and moved-component exclusions stay with this task.
Source: Aschbacher--Smith C.3.5, p.150, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem perfect_odd_rank_of_projection
    {X Y Z : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Group Y] [CommGroup Z] {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (π : X →* Y × Z) (hk : IsPGroup 2 π.ker)
    (hcyc : ∀ U : Subgroup Y, IsPGroup p U → IsCyclic U) :
    primeRank p X ≤ 1 := by
  let χ := (MonoidHom.snd Y Z).comp π
  let : Group.IsPerfect χ.range := Group.IsPerfect.range χ
  let : Subsingleton χ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hχ (x : X) : χ x = 1 :=
    congrArg Subtype.val (Subsingleton.elim (χ.rangeRestrict x) 1)
  let P : Sylow p X := Classical.choice inferInstance
  let f : P →* Y := ((MonoidHom.fst Y Z).comp π).comp (P : Subgroup X).subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hxker : (x : X) ∈ π.ker := Prod.ext hx (hχ x)
    exact Subtype.ext (Subgroup.disjoint_def.mp
      (P.isPGroup'.disjoint_of_coprime hk ho.coprime_two_right) x.property hxker)
  let : IsCyclic f.range := hcyc f.range
    (P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hc : IsCyclic P := isCyclic_of_injective f.rangeRestrict
    (fun x y h => hf (congrArg Subtype.val h))
  exact P.primeRank_le_one_of_isCyclic hc

/-- The perfect actor in a Ree two-local normalizer loses its torus image,
so every odd prime has rank at most one. -/
theorem ree_perfect_two_normalizer_odd_rank {m : ℕ} (hm : 1 ≤ m)
    (X P : Subgroup (ReeF4.Model m)) [Group.IsPerfect X]
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hn : X ≤ normalizer (P : Set (ReeF4.Model m)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p X ≤ 1 := by
  obtain ⟨g,s,hg⟩ := ReeF4.ConverseParabolics.normalizer_cover hm P hne hp
  let j := (MulAut.conj g).toMonoidHom.comp X.subtype
  have hj : ∀ x : X, j x ∈ ReeF4.ConverseParabolics.parabolic m s :=
    fun x => hg (mem_map_of_mem _ (hn x.property))
  let f := j.codRestrict (ReeF4.ConverseParabolics.parabolic m s) hj
  have hf : Function.Injective f := by
    intro x y h
    exact X.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val h))
  cases s with
  | linear =>
    apply perfect_odd_rank_of_projection ho
      ((ReeF4.ConverseParabolics.linearProjection hm).comp f)
      ((ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm).comap_of_injective f hf)
    intro U hU
    exact Matrix.SL2.odd_pGroup_isCyclic_of_injective hU
      (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2)) U.subtype U.subtype_injective
  | suzuki =>
    apply perfect_odd_rank_of_projection ho
      ((ReeF4.ConverseParabolics.suzukiProjection hm).comp f)
      ((ReeF4.ConverseParabolics.suzukiProjection_ker_isPGroup hm).comap_of_injective f hf)
    intro U hU
    obtain ⟨Q,hUQ⟩ := hU.exists_le_sylow
    let : IsCyclic Q := BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two
      (by omega) (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2)) Q
    exact Subgroup.isCyclic_of_le hUQ

/-- The actual Tits embedding preserves the perfect actor and its normalized
two-subgroup, so it inherits the same odd-rank obstruction. -/
theorem tits_perfect_two_normalizer_odd_rank
    (X P : Subgroup Tits.ParrottGroup) [Group.IsPerfect X]
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hn : X ≤ normalizer (P : Set Tits.ParrottGroup))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p X ≤ 1 := by
  obtain ⟨f,hf⟩ := ReeF4.Subfield.exists_tits_embedding 1
  let : Group.IsPerfect (X.map f) := Group.IsPerfect.map f
  have hne' : P.map f ≠ ⊥ := fun he => hne ((map_eq_bot_iff_of_injective P hf).mp he)
  have hb := ree_perfect_two_normalizer_odd_rank (by decide : 1 ≤ 1)
    (X.map f) (P.map f) (hp.map f) hne'
    ((map_mono hn).trans (P.le_normalizer_map f)) ho
  exact (primeRank_congr p (X.equivMapOfInjective f hf)).le.trans hb

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
include D S

theorem no_ordinary_natural_ree
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) {m : ℕ} (hm : 1 ≤ m)
    (ek : K ⧸ center K ≃* ReeF4.Model m) : False := by
  obtain ⟨p,hp,ho,hr⟩ := ordinary_natural_span_rank D S (M := M) e
  let : Fact p.Prime := ⟨hp⟩
  have hb := h.ordinary_span_primeRank_le_of_model_two_normalizers K hK ek ho
    (fun X P hX hP hne hn => by
      let := hX
      exact ree_perfect_two_normalizer_odd_rank hm X P hP hne hn ho)
  omega

theorem no_ordinary_natural_tits
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Tits.ParrottGroup) : False := by
  obtain ⟨p,hp,ho,hr⟩ := ordinary_natural_span_rank D S (M := M) e
  let : Fact p.Prime := ⟨hp⟩
  have hb := h.ordinary_span_primeRank_le_of_model_two_normalizers K hK ek ho
    (fun X P hX hP hne hn => by
      let := hX
      exact tits_perfect_two_normalizer_odd_rank X P hP hne hn ho)
  omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
