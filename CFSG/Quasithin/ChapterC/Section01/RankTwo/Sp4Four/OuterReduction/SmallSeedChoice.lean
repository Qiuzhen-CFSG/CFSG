module

public import Theory.GroupAction.ComponentSmallTwoSection
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups

/-!
# A bad small fixed seed forces the source nonnormalization

The seed and Z_alpha lie in their actual common two-group kernel when the
critical distance is positive. If their join were locally normal, the
component's simple quotient would centralize its section modulo Z_alpha,
contradicting the bad residual displacement. The local generating pair then
forces the endpoint seed to fail to normalize the same literal join.

Source: MS93 (2.1)(vii),(3.4), p.868. This uses only the component quotient,
so the argument precedes outer removal. The seed order and chosen generating
pair remain explicit inputs from their independent model and graph producers.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

theorem bad_seed_join_not_normalized (geometry : Geometry R)
    (hb : 0 < geometry.b R) {a d t : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hp : IsPGroup 2 (Q R t))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ U R d)
    (hcard : (Z R a).relIndex (Y ⊔ Z R a) ≤ 64)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a) :
    ¬ stabilizer R a ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro hn
  have ht : color R t = true := by
    have hc := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have haQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans (omegaCenter_le _)
  have hdQ : Z R d ≤ Q R d :=
    (geometry.omega_bound d hd (by rwa [geometry.distance_constant d hd])).trans (omegaCenter_le _)
  have hDQ : Y ⊔ Z R a ≤ Q R t := sup_le
    ((hY.trans (U_le_Z d)).trans (hdQ.trans (Q_le_adjacent_h R ht hdt)))
    (haQ.trans (Q_le_adjacent_h R ht hat))
  have hQG : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hDG := hDQ.trans hQG
  let := finite_stabilizer R a
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let : Finite (Y ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hDQ) (inclusion_injective _)
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer (R := R) a)) (inclusion_injective _)
  let : ((Z R a).subgroupOf (Y ⊔ Z R a)).Normal :=
    normal_subgroupOf_of_le_normalizer (hDG.trans (Z_normalized R a))
  have hperf : IsPPerfect 2 (Ltilde R a) := by
    let e := (pResidual 2 (stabilizer R a)).equivMapOfInjective
      (stabilizer R a).subtype (stabilizer R a).subtype_injective
    exact (isPPerfect_pResidual (G := stabilizer R a) 2).of_surjective
      e.toMonoidHom e.surjective
  have hc := commutator_component_le_of_seventeen_small_section
    (Ltilde R a) (Y ⊔ Z R a) (Z R a) hperf q hq hker hS (hp.to_le hDQ) hcard
    ((Ltilde_le_stabilizer (R := R) a).trans hn)
    ((Ltilde_le_stabilizer (R := R) a).trans (Z_normalized R a))
  exact hbad ((commutator_mono le_sup_left le_rfl).trans hc)

theorem endpoint_not_normalizes_bad_seed_join (geometry : Geometry R)
    (hb : 0 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hp : IsPGroup 2 (Q R t))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ U R d)
    (hcard : (Z R a).relIndex (Y ⊔ Z R a) ≤ 64)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a)
    (hYn : Q R t ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e) :
    ¬ Z R e ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro he
  apply bad_seed_join_not_normalized geometry hb ha hd hat hdt hp q hq hker hS Y hY hcard hbad
  have hQZ : Q R t ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat)).trans
      (Z_normalized R a)
  exact hgen.trans (sup_le ((le_inf hYn hQZ).trans
    (normalizer_inf_normalizer_le_normalizer_sup Y (Z R a))) he)

theorem endpoint_not_normalizes_bad_seed_of_card (geometry : Geometry R)
    (hb : 0 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hp : IsPGroup 2 (Q R t))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ U R d)
    (hcard : Nat.card Y ≤ 64)
    (hbad : ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a)
    (hYn : Q R t ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e) :
    ¬ Z R e ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  let := finite_stabilizer R d
  let := finite_stabilizer R a
  let : Finite Y := Finite.of_injective
    (inclusion ((hY.trans (U_le_Z d)).trans (Z_le_stabilizer R d))) (inclusion_injective _)
  let : Finite (Z R a) := Finite.of_injective
    (inclusion (Z_le_stabilizer R a)) (inclusion_injective _)
  have ht : color R t = true := by
    have hc := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have haQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans (omegaCenter_le _)
  have hn : Z R a ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    (haQ.trans (Q_le_adjacent_h R ht hat)).trans hYn
  apply endpoint_not_normalizes_bad_seed_join geometry hb ha hd hat hdt hp q hq hker hS
    Y hY _ hbad hYn hgen
  rw [relIndex_sup_of_normalizes Y (Z R a) hn]
  exact (Nat.le_of_dvd (Nat.card_pos (α := Y)) ((Z R a).relIndex_dvd_card Y)).trans hcard

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
