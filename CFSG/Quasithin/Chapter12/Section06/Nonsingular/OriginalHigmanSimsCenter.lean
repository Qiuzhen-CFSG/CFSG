module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsNative
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsTransfer
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsResidual

/-!
# The original covering center lies in the common HS residual

The actual centralizer in K_v is the full inverse image of the native
two-central involution centralizer. Its index in the original perfect K_v
is odd because it contains the same full component Sylow subgroup. The
native cyclic prime-to-three quotient and full-cover transfer therefore
put the entire covering center in the residual of this centralizer.
The established residual-intersection identity places it in the same
ambient common residual, with no kernel or central-line premise added.

Source: the original paired-component comparison for 12.6.12, pp.825–826.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The full original center is contained in the actual ambient common
prime-to-three residual, not merely in its native quotient image. -/
theorem SourceHypothesis.nonsingular_hs_center_le_common_residual
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : G) (hz : z ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hz2 : z ^ 2 = 1) (hznot : z ∉ centralizer (Kv (v : G) : Set G)) :
    (center (Kv (v : G))).map (Kv (v : G)).subtype ≤
      (primeToResidual 3 (Gv (v : G) ⊓ Gv z : Subgroup G)).map
        (Gv (v : G) ⊓ Gv z).subtype := by
  let := hK
  let C := Kv (v : G)
  let M₀ := (Gv z).subgroupOf C
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  obtain ⟨j,hj,hjc,_,_,himage,hfull,_,_,_,_,_⟩ :=
    H.nonsingular_hs_selected_centralizer_image D v hv hK e S z hz hz2 hznot
  let B := centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)
  change B.comap q = M₀ at hfull
  change M₀.map q = B at himage
  have hkq : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hZM : center C ≤ M₀ := by
    rw [←hfull]
    intro x hx
    change q x ∈ B
    rw [show q x = 1 from (show x ∈ q.ker from hkq.symm ▸ hx)]
    exact B.one_mem
  let g : M₀ →* B := (MulEquiv.subgroupCongr himage).toMonoidHom.comp (q.subgroupMap M₀)
  have hg : Function.Surjective g :=
    (MulEquiv.subgroupCongr himage).surjective.comp (q.subgroupMap_surjective M₀)
  have hkg : g.ker ≤ center M₀ := by
    intro x hx
    have hxq : q x.val = 1 := congrArg Subtype.val hx
    have hxc : x.val ∈ center C := hkq ▸ hxq
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hxc y.val)
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hz' : z ∈ S₀ ⊓ centralizer (S₀ : Set G) :=
    map_center_subtype_eq_inf_centralizer S₀ ▸ hz
  have hPM : (P : Subgroup C) ≤ M₀ := by
    intro x hx
    have hxS : (x : G) ∈ S₀ := (hP ▸ mem_map_of_mem C.subtype hx).1
    exact mem_centralizer_singleton_iff.mpr (hz'.2 x hxS)
  have hi : ¬ 2 ∣ M₀.index := fun hh => P.not_dvd_index
    (hh.trans (index_dvd_of_le hPM))
  have hZ2 : IsPGroup 2 (center C) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)]
    decide)
  let : IsCyclic (B ⧸ primeToResidual 3 B) :=
    OriginalHigmanSimsNative.twoCentral_residual_quotient_cyclic j hj hjc
  have hZ := OriginalHigmanSims.central_two_subgroup_le_residual
    M₀ (center C) hZM le_rfl hZ2 hi g hg hkg
  have hZG := map_mono (f := C.subtype) hZ
  rw [map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype,inf_comm (Gv z) C] at hZG
  exact hZG.trans_eq (H.nonsingular_hs_intersection_primeToResidual D v hv hK e (Gv z))

end CFSG.Quasithin.Chapter12.Section06
