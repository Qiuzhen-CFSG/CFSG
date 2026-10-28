module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairSectionActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryPairActor

/-!
# Natural multiplicity in the Chapter 11 linear pair actor

For an actual SL2 pair actor, the literal two-seed quotient is a sum of
natural modules over that actor's unchanged field. Its square-order formula
makes the opposite-seed index a positive power of the field order. If the
multiplicity is one, transitivity on nonzero vectors and the elementary
seed lift make the original pair span elementary. Otherwise the source
seed-square inequality follows.

The linear beta and both nonbinary unitary beta models supply the required
literal maps, including their beta-core kernels. The unitary conclusion
retains the possible elementary pair with equal seed indices. Excluding
that alternative still requires the general (11.3)(e) argument; it is not
an assumption of linear alpha.

Source: DGS85, Groups and Graphs, (5.12)--(5.13), pp.113--115, and
(11.3)(b,g), pp.169--170.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Natural copies on the literal pair section for a marked linear actor. -/
theorem source_pair_linear_natural_copies
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* SL(2,k))
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (R : Sylow 2 SL(2,k))
    (ha : ((Z (family P) a).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f = R) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V), letI := hE
        ∃ σ : Representation (ZMod 2) SL(2,k) (Additive (V ⧸ J.subgroupOf V)),
          ∃ s : BinaryConjugationSection H V J (σ.comp f),
            (∀ x : V, (s.coordinates x).toAdd = Additive.ofMul (QuotientGroup.mk' (J.subgroupOf V) x)) ∧
            fixedSpace σ ⊤ = ⊥ ∧ SL2SylowFixedRecognition.NaturalCoordinates σ := by
  let := finite_endpoints h
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  obtain ⟨hJ,hE,σ,s,hs,hfixed,hquad,hgen⟩ := source_pair_section_for_actor h hB d hc hb hbc hac Ma Mb f hf hk
  let := hJ
  let := hE
  rw [ha] at hquad hgen
  let : Finite V := Finite.of_injective
    (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  let : Finite (V ⧸ J.subgroupOf V) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact ⟨hJ,hE,σ,s,hs,hfixed,sl2_natural_copies σ R hquad hgen hfixed⟩

/-- The opposite-seed index is a positive power of the pair actor field.
Multiplicity one forces the original pair span to be elementary, with its
central kernel and elementary seed proved from the graph. -/
theorem source_pair_linear_seed_power
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* SL(2,k))
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (R : Sylow 2 SL(2,k))
    (ha : ((Z (family P) a).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f = R) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    ∃ r : ℕ, 0 < r ∧
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) = Nat.card k ^ r ∧
      (r = 1 → IsElementaryAbelian 2 V) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let E := Z (family P) a ⊓ Q (family P) b
  let : Finite V := Finite.of_injective
    (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  obtain ⟨hJ,hE,σ,s,_,_,r,e,he⟩ := source_pair_linear_natural_copies
    h hB d hc hb hbc hac Ma Mb f hf hk R ha
  let := hJ
  let := hE
  have hsize := Nat.card_congr e.toEquiv
  simp only [Nat.card_fun,Nat.card_fin] at hsize
  change Nat.card (V ⧸ J.subgroupOf V) = _ at hsize
  rw [source_rankOne_pair_quotient_order h hB d hc hb hbc hac Mb] at hsize
  have hpower : (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) =
      Nat.card k ^ r := by
    apply Nat.pow_left_injective (n := 2) (by decide)
    simpa only [←pow_mul,Nat.mul_comm] using hsize
  have hescape := source_seed_not_le_opposite_core h hbc.symm
    (source_critical_one_adjacent hc hb).symm
    (by intro hp; apply source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb;
        rw [sup_comm]; exact hp)
  have hr : 0 < r := by
    by_contra! hh
    have hr0 : r = 0 := by omega
    rw [hr0,pow_zero] at hpower
    exact hescape (relIndex_eq_one.mp hpower)
  refine ⟨r,hr,hpower,?_⟩
  intro hr1
  subst r
  let coord := e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → k))
  have hcoord : ∀ g v, coord (σ g v) = Matrix.mulVec g.val (coord v) := fun g v => he g v 0
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le (show J ≤ Z (family P) a from inf_le_left)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ Z (family P) a from inf_le_left)
  have hcentral : J ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (Z (family P) a))).trans (centralizer_le inf_le_left))
    · exact inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative (Z (family P) c))).trans (centralizer_le inf_le_right))
  have hesc : ¬ E ≤ J := by
    intro hle
    exact (source_rankOne_seed_escape h hB d hc hb hbc hac Mb).1
      (hle.trans (inf_le_right.trans ((source_Z_Q_U h c).1.trans (map_subtype_le _))))
  exact elementary_core_of_natural_section H V J E σ f hf s hcentral le_sup_left hesc coord hcoord

/-- Source (11.3)(g) for an actual linear pair actor, with the earlier
nonabelian-pair clause isolated as the only remaining alternative. -/
theorem source_pair_linear_seed_square_or_elementary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* SL(2,k))
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (R : Sylow 2 SL(2,k))
    (ha : ((Z (family P) a).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f = R) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
        (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) ∨
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) =
        (Q (family P) b).relIndex (Z (family P) a) ∧
      IsElementaryAbelian 2 (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) := by
  obtain ⟨r,hr,hpower,hsmall⟩ := source_pair_linear_seed_power h hB d hc hb hbc hac Ma Mb f hf hk R ha
  have hcard : (Q (family P) b).relIndex (Z (family P) a) = Nat.card k := by
    have hh := congrArg (fun X : Subgroup SL(2,k) => Nat.card X) ha
    rw [←relIndex_ker,hk,relIndex_subgroupOf
      (show Z (family P) a ≤ (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b from
        le_sup_left.trans le_sup_left)] at hh
    exact hh.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 R).symm.toEquiv)
  by_cases hr1 : r = 1
  · exact Or.inr ⟨by rw [hpower,hr1,pow_one,hcard],hsmall hr1⟩
  · apply Or.inl
    rw [hcard,hpower]
    exact Nat.pow_le_pow_right (Nat.card_pos (α := k)) (by omega)

/-- A linear beta quotient supplies the literal surjective pair map and
its full Sylow image, at the original field. -/
theorem source_linear_pair_actor
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k)) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    ∃ f : H →* SL(2,k), Function.Surjective f ∧
      f.ker = (Q (family P) b).subgroupOf H ∧
      ∃ R : Sylow 2 SL(2,k), ((Z (family P) a).subgroupOf H).map f = R := by
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := Finite.of_injective eb eb.injective
  obtain ⟨hHK,R,T,hRT,hk,ha,hc',hr⟩ := source_pair_actor_map h hB d hc hb hbc hac Mb
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let K := d.localGroup b
  let q := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hHK)
  let f := eb.toMonoidHom.comp q
  let R' := R.mapSurjective (f := eb.toMonoidHom) eb.surjective
  let T' := T.mapSurjective (f := eb.toMonoidHom) eb.surjective
  have hRT' : R' ≠ T' := by
    intro he
    exact hRT (Sylow.ext (map_injective eb.injective (congrArg Sylow.toSubgroup he)))
  have hom (S : Sylow 2 SL(2,k)) : omegaCenterIn (S : Subgroup SL(2,k)) = S := by
    rw [omegaCenterIn_eq_omegaOneAmbient,sl2_omega_center_eq]
  have hm (A : Subgroup H) (S : Sylow 2 (K ⧸ pCore 2 K))
      (hAS : A.map q = omegaCenterIn (S : Subgroup (K ⧸ pCore 2 K))) :
      A.map f = (S.mapSurjective (f := eb.toMonoidHom) eb.surjective : Subgroup SL(2,k)) := by
    rw [show f = eb.toMonoidHom.comp q from rfl,←Subgroup.map_map,hAS,
      NilesRankOneKernel.omegaCenterIn_map_injective eb.toMonoidHom eb.injective]
    exact hom (S.mapSurjective (f := eb.toMonoidHom) eb.surjective)
  refine ⟨f,?_,?_,R',hm _ R ha⟩
  · apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hr,Subgroup.map_sup,
      NilesRankOneKernel.omegaCenterIn_map_injective eb.toMonoidHom eb.injective,
      NilesRankOneKernel.omegaCenterIn_map_injective eb.toMonoidHom eb.injective]
    change omegaCenterIn (R' : Subgroup SL(2,k)) ⊔ omegaCenterIn (T' : Subgroup SL(2,k)) = ⊤
    rw [hom,hom]
    exact Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 R' T' hRT'
  · rw [←hk]
    ext x
    change eb (q x) = 1 ↔ q x = 1
    rw [←eb.map_one,eb.injective.eq_iff]

/-- For either nonbinary unitary carrier, the actual linear block proves
the seed-square inequality unless the original pair span is elementary. -/
theorem source_unitary_seed_square_or_elementary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 2 ≤ n)
    (hi : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
        (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) ∨
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) =
        (Q (family P) b).relIndex (Z (family P) a) ∧
      IsElementaryAbelian 2 (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    hi.elim (.projective_unitary n (by omega)) (.special_unitary n (by omega))
  obtain ⟨_,f,hf,hk,R,T,ha,_⟩ := source_unitary_pair_linear_actor h hB d hc hb hbc hac hn hi
  exact source_pair_linear_seed_square_or_elementary h hB d hc hb hbc hac Ma Mb f hf hk R ha

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
