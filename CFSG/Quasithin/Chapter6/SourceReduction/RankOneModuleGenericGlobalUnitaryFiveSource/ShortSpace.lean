module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortSpace
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCosets
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.QuotientTransport

/-!
# The orthogonal space at the original marked U₅ short root

Restrict the selected reduced endpoint comparison to its actual solvable
residual, and use the geometric plane semidirect product. The short identity
block maps to the same original short root selected by the whole-middle map.
Its residual centralizer therefore contains the transported orthogonal
three-space and full fixed line, of orders 64 and 4. The same literal
coordinates give a perfect orbit after killing that full line.

This constructs the residual geometry needed by the two F.4.42 quotients.
It does not identify C_L(t) with C_{N_G(L)}(t), assert invariance under the
latter, or establish ambient short-centralizer containment. Those full
stabilizer and quotient arguments remain required.
Source: Aschbacher–Smith F.4.42, printed pp.295–296 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
namespace UnitaryFiveShortSpace
variable (U : Model 4) {P L : Subgroup G} (e : P ≃* U.rightParabolic)
    (hr : (solvableResidual P).map P.subtype = L)

/-- The same residual restriction of the original endpoint comparison. -/
def coordinates : PlaneCore.PlaneSemidirect U.form ≃* L :=
  U.rightLocalEquiv.trans (U.rightLocalImageEquiv.trans (UnitaryFiveActor.rightFactorEquiv U e hr).symm)

theorem coordinates_val (x : PlaneCore.PlaneSemidirect U.form) :
    (coordinates U e hr x).val = (e.symm (U.rightLocalEquiv x).val).val := by
  rw [coordinates,MulEquiv.trans_apply,MulEquiv.trans_apply,
    UnitaryFiveActor.rightFactorEquiv_symm_val]
  rfl

theorem coordinates_short_val :
    (coordinates U e hr (SemidirectProduct.inl (InvolutionGeometry.shortParameter U.form))).val =
      (e.symm U.shortInvolution).val := by
  rw [coordinates,MulEquiv.trans_apply,MulEquiv.trans_apply,
    UnitaryFiveActor.rightFactorEquiv_symm_val]
  congr 2
  apply Subtype.ext
  change (U.rightLocalEquiv (SemidirectProduct.inl (InvolutionGeometry.shortParameter U.form))).val.val = _
  rw [U.rightLocalEquiv_val]
  simp only [SemidirectProduct.left_inl,SemidirectProduct.right_inl,map_one,mul_one]
  rfl

/-- Restriction to the literal centralizer of a compatibly marked source element. -/
def centralizerCoordinates (t : L) (ht : t.val = (e.symm U.shortInvolution).val) :
    ShortSpace.centralizer U.form ≃* Subgroup.centralizer ({t} : Set L) :=
  ((coordinates U e hr).subgroupMap (ShortSpace.centralizer U.form)).trans
    (MulEquiv.subgroupCongr
      ((CentralizerSmallKernelTransport.map_centralizer (coordinates U e hr)
        (SemidirectProduct.inl (InvolutionGeometry.shortParameter U.form))).trans
        (congrArg (fun x : L => Subgroup.centralizer ({x} : Set L))
          (Subtype.ext ((coordinates_short_val U e hr).trans ht.symm)))))

theorem centralizerCoordinates_val (t : L) (ht : t.val = (e.symm U.shortInvolution).val)
    (x : ShortSpace.centralizer U.form) :
    (centralizerCoordinates U e hr t ht x).val = coordinates U e hr x.val := rfl

theorem centralizerCoordinates_short (t : L) (ht : t.val = (e.symm U.shortInvolution).val) :
    centralizerCoordinates U e hr t ht (ShortSpace.shortMark U.form) =
      ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (coordinates_short_val U e hr).trans ht.symm

private theorem map_fixed_residual {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (V B : Subgroup X)
    (h : V ⊓ Subgroup.centralizer (primeToResidual 2 X : Set X) = B) :
    V.map a.toMonoidHom ⊓ Subgroup.centralizer (primeToResidual 2 Y : Set Y) = B.map a.toMonoidHom := by
  apply le_antisymm
  · rintro y ⟨⟨x,hx,rfl⟩,hy⟩
    refine ⟨x,h.le ⟨hx,?_⟩,rfl⟩
    intro b hb
    apply a.injective
    simp only [map_mul]
    exact hy (a b) ((map_primeToResidual a).le (mem_map_of_mem a.toMonoidHom hb))
  · rintro y ⟨x,hx,rfl⟩
    have hh := h.ge hx
    refine ⟨mem_map_of_mem a.toMonoidHom hh.1,?_⟩
    intro b hb
    obtain ⟨c,hc,rfl⟩ := (map_primeToResidual a).ge hb
    exact (a.map_mul c x).symm.trans ((congrArg a (hh.2 c hc)).trans (a.map_mul x c))

/-- The intrinsic residual geometry used before the two F.4.42 quotients. -/
def Geometry (t : L)
    (a : ShortSpace.centralizer U.form ≃* Subgroup.centralizer ({t} : Set L)) : Prop :=
    let V := (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom
    let B := (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom
    V = normalClosure ({a (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)} :
      Set (Subgroup.centralizer ({t} : Set L))) ∧
    IsElementaryAbelian 2 V ∧ Nat.card V = 64 ∧ Nat.card B = 4 ∧ B.relIndex V = 16 ∧
    B ≤ V ∧ B ≤ center (Subgroup.centralizer ({t} : Set L)) ∧
    V ⊓ Subgroup.centralizer (primeToResidual 2 (Subgroup.centralizer ({t} : Set L)) : Set _) = B ∧
    (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({t} : Set L)) ∈ B

/-- The constructed source three-space and full line, on this same marking. -/
theorem geometry (t : L) (ht : t.val = (e.symm U.shortInvolution).val) :
    Geometry U t (centralizerCoordinates U e hr t ht) := by
  let a := centralizerCoordinates U e hr t ht
  let V := (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom
  let B := (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom
  have hV : V = normalClosure ({a (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)} : Set _) := by
    dsimp only [V]
    rw [←ShortSpace.long_normalClosure,map_normalClosure _ _ a.surjective,Set.image_singleton]
    rfl
  let : IsElementaryAbelian 2 (ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec) :=
    ShortSpace.space_elementary U.form U.rightLeviTrace U.rightLeviTrace_spec
  have hK : Nat.card (FixedBy.subfield U.F U.form.conj) = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius U.form.conj 2 2 (by decide)
      (by simpa using U.card) U.conjugation
  have hVc : Nat.card V = 64 := by
    rw [card_map_of_injective a.injective,ShortSpace.space_card,hK]
    norm_num
  have hBc : Nat.card B = 4 := by
    rw [card_map_of_injective a.injective,ShortSpace.line_card,hK]
  have hBV : B ≤ V := map_mono (ShortSpace.line_le_space U.form U.rightLeviTrace U.rightLeviTrace_spec)
  have hindex : B.relIndex V = 16 := by
    have hi := (B.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBV).toEquiv,hBc,hVc] at hi
    change 4 * B.relIndex V = 64 at hi
    omega
  refine ⟨hV,IsElementaryAbelian.map a.toMonoidHom,hVc,hBc,hindex,hBV,?_,
    map_fixed_residual a _ _ (ShortSpace.fixed_primeTo U.form U.rightLeviTrace U.rightLeviTrace_spec),?_⟩
  · rintro y ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b,rfl⟩ := a.surjective b
    exact (a.map_mul b x).symm.trans ((congrArg a
      (mem_center_iff.mp (ShortSpace.line_le_center U.form U.rightLeviTrace U.rightLeviTrace_spec hx) b)).trans
        (a.map_mul x b))
  · rw [←centralizerCoordinates_short U e hr t ht]
    exact mem_map_of_mem a.toMonoidHom (ShortSpace.shortMark_mem_line U.form U.rightLeviTrace U.rightLeviTrace_spec)

/-- The same transported quotient has a perfect transitive actor whenever
its literal full line is killed by the chosen quotient map. -/
theorem quotient_perfect_orbit (t : L) (ht : t.val = (e.symm U.shortInvolution).val)
    {B : Type*} [Group B] (f : Subgroup.centralizer ({t} : Set L) →* B)
    (hline : (ShortSpace.line U.form U.rightLeviTrace U.rightLeviTrace_spec).map
      (centralizerCoordinates U e hr t ht).toMonoidHom ≤ f.ker) :
    let a := centralizerCoordinates U e hr t ht
    ∃ D : Subgroup B, Group.IsPerfect D ∧ D ≤ f.range ∧
      ∀ v ∈ ((ShortSpace.space U.form U.rightLeviTrace U.rightLeviTrace_spec).map a.toMonoidHom).map f,
        v ≠ 1 → ∃ b ∈ D, b * f (a (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)) * b⁻¹ = v := by
  let a := centralizerCoordinates U e hr t ht
  have hK : 3 < Nat.card (FixedBy.subfield U.F U.form.conj) := by
    have hcard : Nat.card (FixedBy.subfield U.F U.form.conj) = 4 :=
      FiniteField.card_fixed_of_quadratic_frobenius U.form.conj 2 2 (by decide)
        (by simpa using U.card) U.conjugation
    omega
  obtain ⟨D,hD,hDf,hDorb⟩ := ShortSpace.quotient_perfect_orbit U.form U.rightLeviTrace
    U.rightLeviTrace_spec hK (f.comp a.toMonoidHom) (by
      intro x hx
      exact hline (mem_map_of_mem a.toMonoidHom hx))
  refine ⟨D,hD,hDf.trans (by rintro _ ⟨x,rfl⟩; exact ⟨a x,rfl⟩),?_⟩
  intro v hv hv1
  rw [map_map] at hv
  exact hDorb v hv hv1

/-- The transported generator is in the actual marked long-root class. -/
theorem longMark_isConj (t : L) (ht : t.val = (e.symm U.shortInvolution).val) :
    IsConj (e.symm U.longInvolution).val
      (centralizerCoordinates U e hr t ht
        (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)).val.val := by
  let z : PlaneCore.PlaneSemidirect U.form := SemidirectProduct.inl
    (PlaneCore.Parameters.diagonalParameter U.form 0 (map_zero _))
  let A := ShortSpace.basis U.form U.rightLeviTrace U.rightLeviTrace_spec
  have hc : IsConj z (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec).val := by
    apply isConj_iff.mpr
    refine ⟨SemidirectProduct.inr A,?_⟩
    rw [←map_inv,←SemidirectProduct.inl_aut]
    rfl
  have he : (coordinates U e hr z).val = (e.symm U.longInvolution).val := by
    rw [coordinates_val]
    congr 2
    apply Subtype.ext
    rw [U.rightLocalEquiv_val]
    simp only [z,SemidirectProduct.left_inl,SemidirectProduct.right_inl,map_one,mul_one]
    rfl
  have hh := L.subtype.map_isConj ((coordinates U e hr).toMonoidHom.map_isConj hc)
  change IsConj (coordinates U e hr z).val
    (coordinates U e hr (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec).val).val at hh
  rw [he,←centralizerCoordinates_val U e hr t ht] at hh
  exact hh

end UnitaryFiveShortSpace
variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The actual selected short root carries the native orthogonal space and
its entire fixed line, through the same original endpoint comparison. -/
theorem Preparation.unitaryFive_short_geometry_at
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val)
    (t : (normalizerAmalgam L (residual H)).M₁₂)
    (ht : t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hshort : (F.middle t).val = MulAut.conj U.shortInvolution.val) :
    ∃ tL : L, tL.val = t.val ∧
    ∃ j : ShortSpace.centralizer U.form ≃* Subgroup.centralizer ({tL} : Set L),
      (∀ x, (j x).val.val = (a.comparison.left.symm (U.rightLocalEquiv x.val).val).val) ∧
      IsConj (a.comparison.left.symm U.longInvolution).val
        (j (ShortSpace.longMark U.form U.rightLeviTrace U.rightLeviTrace_spec)).val.val ∧
      UnitaryFiveShortSpace.Geometry U tL j := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  let tL : L := ⟨t.val,pCoreIn_le 2 L (map_subtype_le _ ht)⟩
  let tP : P := ⟨t.val,hLP tL.property⟩
  have hmark : a.comparison.left tP = U.shortInvolution := by
    apply Subtype.ext
    apply five_conj_injective U
    calc
      _ = (F.left (inclusion r.left_le tP)).val := (h0 tP).symm
      _ = (F.middle t).val := congrArg Subtype.val (F.left_commutes t)
      _ = _ := hshort
  have htval : tL.val = (a.comparison.left.symm U.shortInvolution).val := by
    have he : tP = a.comparison.left.symm U.shortInvolution :=
      a.comparison.left.injective (hmark.trans (a.comparison.left.apply_symm_apply _).symm)
    exact congrArg Subtype.val he
  have hr : (solvableResidual P).map P.subtype = L :=
    d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
  let j := UnitaryFiveShortSpace.centralizerCoordinates U a.comparison.left hr tL htval
  refine ⟨tL,rfl,j,?_,UnitaryFiveShortSpace.longMark_isConj U a.comparison.left hr tL htval,
    UnitaryFiveShortSpace.geometry U a.comparison.left hr tL htval⟩
  intro x
  rw [show (j x).val = UnitaryFiveShortSpace.coordinates U a.comparison.left hr x.val from
    UnitaryFiveShortSpace.centralizerCoordinates_val U a.comparison.left hr tL htval x]
  exact UnitaryFiveShortSpace.coordinates_val U a.comparison.left hr x.val

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
