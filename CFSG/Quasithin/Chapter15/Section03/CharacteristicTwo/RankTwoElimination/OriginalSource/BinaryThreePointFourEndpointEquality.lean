module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointExactFlags
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.EndpointResidualEquality

/-!
# The actual binary-four smaller component is the endpoint parabolic

The original restricted Sylow join has its own PSL3(2) quotient and B is
its literal two-residual. The endpoint residual calculation therefore
identifies B with the whole join, retaining the original Sylow restriction.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterC BinaryMS.MS93
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

private theorem endpoint_image_eq
    {X : Type*} [Group X] [Finite X] (D J : Subgroup X)
    (a : X ≃* LinearGroup 4) (v : Basis 3) (last : Bool)
    (e : (J ⧸ pCore 2 J) ≃* PSL(3,ZMod 2))
    (hres : (pResidual 2 J).map J.subtype=D)
    (hj : J.map a.toMonoidHom=cutStabilizer v ({if last then 2 else 0} : Set (Fin 3))) :
    D.map a.toMonoidHom=cutStabilizer v ({if last then 2 else 0} : Set (Fin 3)) := by
  let i := (J.equivMapOfInjective a.toMonoidHom a.injective).trans (MulEquiv.subgroupCongr hj)
  let ep := ((QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).symm.trans e).trans
    Matrix.PSL3Two.equiv.symm
  have he := BinaryLinear.SevenFlagCore.endpoint_residual_eq_self_of_quotient v last ep
  have hm : (pResidual 2 (J.map a.toMonoidHom)).map (J.map a.toMonoidHom).subtype=
      D.map a.toMonoidHom := by rw [←map_embedded_pResidual,hres]
  exact hm.symm.trans ((congrArg
    (fun A : Subgroup (LinearGroup 4) => (pResidual 2 A).map A.subtype) hj).trans he)

variable {G : Type*} [Group G] [Finite G]

/-- The actual restricted Sylow lies in B, and B itself is one of the
literal endpoint parabolics in the same full-Sylow basis. -/
theorem binary_three_point_four_endpoint_equality
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    ∃ T : Sylow 2 K, (T : Subgroup K)=(S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K ∧
      (T : Subgroup K) ≤ B.subgroupOf K ∧
      ∃ (a : K ≃* LinearGroup 4) (v : Basis 3),
        (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup (LinearGroup 4))=
          cutStabilizer v Set.univ ∧
        ((B.subgroupOf K).map a.toMonoidHom=cutStabilizer v ({0} : Set (Fin 3)) ∨
         (B.subgroupOf K).map a.toMonoidHom=cutStabilizer v ({2} : Set (Fin 3))) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (L.subgroupOf C).map q
  let D := B.subgroupOf K
  obtain ⟨T,hT,a,v,hv,hflag⟩ := binary_three_point_four_endpoint_flags d L b z hLS P hP K hBK hm
  obtain ⟨_,T₁,hT₁,hres⟩ := binary_three_point_join_residual d L b z hLS P hP K hBK
  have hTT : T₁=T := Sylow.ext (hT₁.trans hT.symm)
  subst T₁
  obtain ⟨T₂,hT₂,⟨eJ⟩⟩ := binary_three_point_containing_join_core_quotient d L b z hLS P hP K hBK
  have hTT₂ : T₂=T := Sylow.ext (hT₂.trans hT.symm)
  subst T₂
  let J := D ⊔ (T : Subgroup K)
  have hmapT : (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
      (T : Subgroup K).map a.toMonoidHom := rfl
  have hflags : D.map a.toMonoidHom=cutStabilizer v ({0} : Set (Fin 3)) ∨
      D.map a.toMonoidHom=cutStabilizer v ({2} : Set (Fin 3)) := by
    rcases hflag with hflag | hflag
    · exact Or.inl (endpoint_image_eq D J a v false eJ hres
        (by simpa only [J,D,B,q,C,Subgroup.map_sup,hmapT,Bool.false_eq_true,↓reduceIte] using hflag))
    · exact Or.inr (endpoint_image_eq D J a v true eJ hres
        (by simpa only [J,D,B,q,C,Subgroup.map_sup,hmapT,↓reduceIte] using hflag))
  have hTD : (T : Subgroup K) ≤ D := by
    apply (Subgroup.map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    rw [←hmapT,hv]
    rcases hflags with he | he <;> rw [he] <;>
      intro x hx <;> simp only [cutStabilizer,mem_iInf] at hx ⊢ <;>
      exact fun k _ => hx k (Set.mem_univ k)
  exact ⟨T,hT,hTD,a,v,hv,hflags⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
