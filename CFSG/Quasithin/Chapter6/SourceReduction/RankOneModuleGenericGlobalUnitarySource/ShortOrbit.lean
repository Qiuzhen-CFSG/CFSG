module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient

/-!
# Unique long-root lifts on the prepared short-line quotient

Use the same reduced comparison to mark both original roots. The long-root
class in C_L(t) has q²−1 elements and its centralizer contains a Sylow of
C_L(t). On the literal N_{C_G(t)}(U)/U quotient, every nonzero vector of
the orthogonal module has exactly one lift in this original long-root class.
Injectivity on that class also proves the exact centralizer preimage under
the original quotient map. The full q-element kernel is retained.

Source: Aschbacher–Smith F.4.42, printed pp.295–296. These supply the
local orbit and quotient-fiber calculations for the ambient argument.
Unique fixed cosets in C_G(t)/C_{N_G(L)}(t), outer transfer, and full
ambient short-centralizer containment remain further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The same prepared full-line quotient has unique long-root lifts and
exact residual centralizer preimages, with the local Sylow placement proved. -/
theorem Preparation.unitary_short_quotient_long_lifts
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∃ P : Sylow 2 (centralizer ({t} : Set L)),
        (P : Subgroup _) ≤ centralizer ({z} : Set _)) ∧
      (∀ v ∈ V.map f, v ≠ 1 →
        ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      (centralizer ({f z} : Set _)).comap f = centralizer ({z} : Set _) := by
  obtain ⟨hm',hn,e,_,_,_,hcommon⟩ :=
    d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,hfusion,_,_,hclass,hSylow,hlift,_⟩ :=
    short_quotient_from_marked_equiv m hm hm' a
  have hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype := by
    rw [hzmark]
    exact haz
  have hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
      normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon z.val.val hzc hz
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card (V.map f) = (2^m)^2 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have hfusion := hfusion f hker.ge
  have hzne : f z ≠ 1 := by
    let : Nontrivial (V.map f) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcV]
      exact Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide)))
    obtain ⟨v,hv⟩ := exists_ne (1 : V.map f)
    have hvne : v.val ≠ 1 := fun he => hv (Subtype.ext he)
    obtain ⟨a,ha,he⟩ := hfusion v.val v.property hvne
    intro hzero
    rw [hzero,mul_one,mul_inv_cancel] at he
    exact hvne he.symm
  have htkill : f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 :=
    MonoidHom.mem_ker.mp (hker.ge (htU.le (mem_zpowers _)))
  have hlifts := hlift f hker
  refine ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hUV,hV,hVQ,hVc,hUc,hker,
    IsElementaryAbelian.map f,hcV,htU,htkill,hzne,hclass,hSylow,hlifts,?_⟩
  ext b
  constructor
  · intro hb
    have hc := mem_centralizer_singleton_iff.mp hb
    have hfix : f (b*z*b⁻¹) = f z := by
      rw [map_mul,map_mul,map_inv,hc,mul_inv_cancel_right]
    have hu := hlifts (f z) (mem_map_of_mem f (subset_normalClosure (Set.mem_singleton z))) hzne
    have he : b*z*b⁻¹ = z := hu.unique ⟨isConj_iff.mpr ⟨b,rfl⟩,hfix⟩ ⟨IsConj.refl z,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  · intro hb
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hb)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
