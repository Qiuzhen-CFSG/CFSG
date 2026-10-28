module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpComponents
public import Theory.GroupTheory.CoprimeQuotientSubgroups.ElementLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicPlacement

/-!
# A cubic in the original exterior pushing-up residual

The product of two elementary matrices on a two-plane has order three and
fixes four independent exterior-square vectors. Lift that matrix through the
literal intersection residual's two-core quotient, using its inclusion-induced
PSL₅(2) marking. Equivariance puts sixteen fixed elements in the original V.

The ordinary J₄ component contains this same cubic. Its covering center is a
two-group because the original H has trivial odd core. Native cubic fusion
therefore places a quasisimple M₂₂ covering subgroup inside the full centralizer
residual of that very cubic. All ambient embeddings, the full central cover,
and the full module of order at least 1024 are retained in the output.

OddNormalizer applies this construction to the literal Hall counterexample.
The whole cubic-residual identification, ambient normality and terminal
commutator contradiction on p.612 remain open. The distinct odd-local argument
on p.623 is not replaced by this order-three construction.

Source: Aschbacher--Smith, 4.2.13, printed p.612, with the original exterior
marking from 12.2.11(a), printed pp.798--799.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter12.Section02
open Representation.SL5TenDimensional
open Representation.SL5ExteriorSquare

private def cubic : Representation.SL5TenDimensional.Group :=
  elementary 0 1 * elementary 1 0
private theorem cubic_pow : cubic ^ 3 = 1 := by decide
private theorem cubic_ne : cubic ≠ 1 := by decide
private def fixedCoordinates (w : Fin 4 → ZMod 2) : Fin 10 → ZMod 2 :=
  ![w 0,0,0,0,0,0,0,w 1,w 2,w 3]
private theorem fixedCoordinates_injective : Function.Injective fixedCoordinates := by
  intro a b hab
  funext i
  fin_cases i
  · exact congrFun hab 0
  · exact congrFun hab 7
  · exact congrFun hab 8
  · exact congrFun hab 9
private theorem cubic_fixedCoordinates : ∀ w : Fin 4 → ZMod 2,
    (actionMatrix cubic).mulVec (fixedCoordinates w) = fixedCoordinates w := by decide

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Every literal covering residual contains a cubic fixing at least sixteen
vectors of the original exterior module. The chosen cubic is lifted through
the original two-core quotient and its inclusion-induced marking. -/
theorem ExteriorMarking.cover_cubic_fixed (a : ExteriorMarking D)
    {F : Subgroup G} (hFL : F ≤ L)
    (hcover : (L : Set G) ⊆ (F : Set G) * (L.pCoreIn 2 : Set G)) :
    ∃ x : F, orderOf x = 3 ∧
      16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) := by
  obtain ⟨e,he⟩ := (a.cover_quotient hFL hcover).1
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime 3 (Nat.card f.ker) := by
    have hk : f.ker = pCore 2 F := by
      exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := F)).exists_card_eq
    rw [hk,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨x,hfx,hxpow⟩ := exists_prime_exponent_lift f hf hk cubic cubic_pow
  have hx : orderOf x = 3 := orderOf_eq_prime_iff.mpr ⟨hxpow,by
    intro h1
    apply cubic_ne
    rw [←hfx,h1,map_one]⟩
  have hxq : a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hFL x)) = cubic :=
    (he x).symm.trans hfx
  let w (t : Fin 4 → ZMod 2) : V :=
    a.coordinates.symm (Multiplicative.ofAdd (coordinates.symm (fixedCoordinates t)))
  have hw (t : Fin 4 → ZMod 2) : (w t : G) ∈ centralizer ({(x : G)} : Set G) := by
    have hact : exteriorAction 2 cubic (coordinates.symm (fixedCoordinates t)) =
        coordinates.symm (fixedCoordinates t) := by
      apply coordinates.injective
      rw [coordinates_action,coordinates.apply_symm_apply,cubic_fixedCoordinates]
    have hh := a.equivariant (inclusion hFL x) (w t)
    rw [hxq] at hh
    change a.coordinates _ = Multiplicative.ofAdd
      (exteriorAction 2 cubic (a.coordinates (a.coordinates.symm _)).toAdd) at hh
    simp only [a.coordinates.apply_symm_apply,toAdd_ofAdd,hact] at hh
    have hh' := a.coordinates.injective (hh.trans (a.coordinates.apply_symm_apply _).symm)
    have hcomm : (x : G) * (w t : G) = (w t : G) * (x : G) := by
      exact mul_inv_eq_iff_eq_mul.mp (congrArg V.subtype hh')
    exact mem_centralizer_singleton_iff.mpr hcomm.symm
  let j : (Fin 4 → ZMod 2) → (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) :=
    fun t => ⟨w t,(w t).property,hw t⟩
  have hj : Function.Injective j := by
    intro t u htu
    have heq : w t = w u := Subtype.ext (congrArg (fun v : (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) => (v : G)) htu)
    have hh := congrArg (fun v : V => coordinates (a.coordinates v).toAdd) heq
    change coordinates ((a.coordinates (a.coordinates.symm _)).toAdd) =
      coordinates ((a.coordinates (a.coordinates.symm _)).toAdd) at hh
    simp only [a.coordinates.apply_symm_apply,toAdd_ofAdd,coordinates.apply_symm_apply] at hh
    exact fixedCoordinates_injective hh
  refine ⟨x,hx,?_⟩
  have hc := Nat.card_le_card_of_injective j hj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.reducePow] using hc



open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- The prescribed cubic lies in the actual intersection residual. Its fixed
vectors belong to the original exterior module, and its M₂₂ cover is a literal
subgroup of the same full J₄ component. -/
theorem exterior_pushingUp_fixed_cubic (s : SylowExteriorMarking D)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
      16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
      ∃ B : Subgroup K, IsQuasisimple B ∧ B ≤ (solvableResidual (centralizer ({k} : Set K))).map
        (centralizer ({k} : Set K)).subtype ∧
        Nonempty ((B ⧸ center B) ≃* Sporadic.Mathieu.M22) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hc := hw.2.2.2.2.2.2.1
  have hcover := hw.2.2.2.2.2.2.2.1
  obtain ⟨x,hx,hfix⟩ := s.marking.cover_cubic_fixed hFL hcover.subset
  have hFK : F.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  let j : F →* K := (inclusion hFH).codRestrict K (fun f => hFK f.property)
  have hj : Function.Injective j := by
    intro x y hxy
    exact (inclusion_injective hFH) (congrArg K.subtype hxy)
  let k := j x
  have hk : orderOf k = 3 := (orderOf_injective j hj x).trans hx
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : q.ker = center K :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hthree : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hq,hz,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact ⟨x,k,rfl,hx,hk,hfix,
    Janko4.LocalStructure.cubic_residual_contains_mathieu_cover q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) hq.le hthree k hk⟩

/-- The two cubic inputs at the original p.612 witnesses, retaining their
literal embedding and the nontrivial fixed part of the exterior module. -/
@[expose] def ExteriorPushingUpCubicCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ s.marking.M.subgroupOf H ∧
    1024 ≤ Nat.card W ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    Nonempty ((F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ s.marking.M).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      V ≤ K.map H.subtype ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (x : F) (k : K), ((k : H) : G) = (x : G) ∧ orderOf x = 3 ∧ orderOf k = 3 ∧
        16 ≤ Nat.card (V ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ∧
        ∃ B : Subgroup K, IsQuasisimple B ∧ B ≤ (solvableResidual (centralizer ({k} : Set K))).map
        (centralizer ({k} : Set K)).subtype ∧
          Nonempty ((B ⧸ center B) ≃* Sporadic.Mathieu.M22)

/-- Construct the cubic and its literal M₂₂ cover in the ordinary branch;
none of its fixed-space, placement or quotient data is an extra premise. -/
theorem exterior_pushingUp_cubic_case (s : SylowExteriorMarking D)
    {A : Subgroup G} (hj : ExteriorPushingUpJankoCase s A) : ExteriorPushingUpCubicCase s A := by
  obtain ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit⟩ := hj
  exact ⟨J,H,W,hw,hf,hsize,hquot,K,hK,hn,hout,hF,hW,hV,⟨e⟩,hsplit,
    exterior_pushingUp_fixed_cubic s hw K hK e⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
