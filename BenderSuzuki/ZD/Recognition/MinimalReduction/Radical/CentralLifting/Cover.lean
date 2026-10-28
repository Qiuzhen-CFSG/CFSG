module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The component above a normal Bender factor

The derived subgroup of the full preimage of a perfect normal subgroup is
perfect and still maps onto that subgroup. For a central extension and an
actual simple Bender factor, this constructs a normal quasisimple subgroup,
hence a component, with an explicit central covering map.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, printed p. 35. This constructs
the covering component only; simplicity of the cover is a separate obligation.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory

private theorem bender_quasisimple {B : Type*} [Group B] [Finite B]
    (hB : IsSimpleBenderGroup B) : IsQuasisimple B := by
  let : IsSimpleGroup B := hB.isSimple
  obtain ⟨n, hn, hm⟩ := hB.exists_exponent
  have hc : Subgroup.center B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center B) inferInstance with hc | hc
    · exact hc
    · exact (hB.not_commutative (fun x y => by
        have hx : x ∈ Subgroup.center B := hc ▸ Subgroup.mem_top x
        exact (Subgroup.mem_center_iff.mp hx y).symm)).elim
  exact { commutator_eq_top := hm.isPerfect hn
          simple := ((QuotientGroup.quotientMulEquivOfEq hc).trans
            (QuotientGroup.quotientBot (G := B))).isSimpleGroup }

variable {G B : Type*} [Group G] [Group B] [Finite B]

/-- The derived subgroup of the full preimage of the specified factor. -/
@[expose] public def centralLiftComponent (q : G →* B) (D : Subgroup B) : Subgroup G :=
  ⁅D.comap q, D.comap q⁆

public instance centralLiftComponent_normal (q : G →* B) (D : Subgroup B) [D.Normal] :
    (centralLiftComponent q D).Normal := by unfold centralLiftComponent; infer_instance

omit [Finite B] in
/-- The covering subgroup lies in the full preimage of the factor. -/
public theorem centralLiftComponent_le (q : G →* B) (D : Subgroup B) :
    centralLiftComponent q D ≤ D.comap q := Subgroup.commutator_le_self _

/-- The constructed subgroup covers the actual Bender factor. -/
public theorem centralLiftComponent_map (q : G →* B) (hq : Function.Surjective q)
    (D : Subgroup B) (hD : IsSimpleBenderGroup D) :
    (centralLiftComponent q D).map q = D := by
  let : IsQuasisimple D := bender_quasisimple hD
  have hmap : (D.comap q).map q = D :=
    Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
  rw [centralLiftComponent, Subgroup.map_commutator, hmap, Subgroup.commutator_eq_self]

/-- Restriction of the original projection to the covering subgroup. -/
@[expose] public def centralLiftProjection (q : G →* B) (D : Subgroup B) :
    centralLiftComponent q D →* D :=
  (q.comp (centralLiftComponent q D).subtype).codRestrict D
    (fun x => centralLiftComponent_le q D x.property)

/-- The restricted projection is onto. -/
public theorem centralLiftProjection_surjective (q : G →* B) (hq : Function.Surjective q)
    (D : Subgroup B) (hD : IsSimpleBenderGroup D) :
    Function.Surjective (centralLiftProjection q D) := by
  intro d
  have hd : (d : B) ∈ (centralLiftComponent q D).map q := by
    rw [centralLiftComponent_map q hq D hD]; exact d.property
  obtain ⟨g, hg, he⟩ := hd
  exact ⟨⟨g, hg⟩, Subtype.ext he⟩

/-- Perfectness follows from the central-extension commutator theorem. -/
public theorem centralLiftComponent_perfect (q : G →* B) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G)
    (D : Subgroup B) (hD : IsSimpleBenderGroup D) :
    Group.IsPerfect (centralLiftComponent q D) := by
  let : IsQuasisimple D := bender_quasisimple hD
  let H := D.comap q
  let f : H →* D := (q.comp H.subtype).codRestrict D (fun x => x.property)
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨g, hg⟩ := hq d
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change q g ∈ D
    rw [hg]; exact d.property
  have hfker : f.ker ≤ Subgroup.center H := by
    intro x hx
    have hxq : (x : G) ∈ q.ker := congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr (fun y => Subtype.ext
      (Subgroup.mem_center_iff.mp (hker hxq) y))
  let := PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center f hf hfker
  have hperf := Group.IsPerfect.map (H := commutator H) H.subtype
  rw [Subgroup.map_subtype_commutator] at hperf
  exact hperf

/-- The explicit perfect central covering, with the original quotient map. -/
@[expose] public def centralLiftCover (q : G →* B) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G)
    (D : Subgroup B) (hD : IsSimpleBenderGroup D) :
    PerfectCentralCovering.Cover (centralLiftComponent q D) D where
  toMonoidHom := centralLiftProjection q D
  surjective := centralLiftProjection_surjective q hq D hD
  isPerfect := centralLiftComponent_perfect q hq hker D hD
  ker_le_center := by
    intro x hx
    have hxq : (x : G) ∈ q.ker := congrArg Subtype.val hx
    exact Subgroup.mem_center_iff.mpr (fun y => Subtype.ext
      (Subgroup.mem_center_iff.mp (hker hxq) y))

/-- Above a normal Bender factor the construction gives a component. -/
public theorem centralLiftComponent_isComponent (q : G →* B) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G)
    (D : Subgroup B) [D.Normal] (hD : IsSimpleBenderGroup D) :
    IsComponent G (centralLiftComponent q D) := by
  let : IsQuasisimple D := bender_quasisimple hD
  exact ⟨Subgroup.Normal.isSubnormal inferInstance, (centralLiftCover q hq hker D hD).isQuasisimple⟩

end BenderSuzuki.ZD
