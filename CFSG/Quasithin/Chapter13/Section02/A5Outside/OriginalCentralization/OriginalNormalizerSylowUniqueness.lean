module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import Theory.Quasithin.EvenCharacteristic

/-!
# Original uniqueness at every ambient Sylow inside N(L)

Conjugacy inside the original N(L) carries the chosen T to any ambient
Sylow S contained in N(L), preserving L itself and its normalizer. Thus
the genuine original uniqueness over L T transports to L S. No new
chosen module, quotient marking or classification hypothesis is needed.

This keeps the Sylow change in the original ambient group, for the
selected-pair core argument. Source: Sylow conjugacy and 1.2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The original unique maximal two-local remains N(L) after any ambient
Sylow change within that same normalizer. -/
theorem original_normalizer_sylow_unique
    (d : Context T L V V₁ V₂ V₃) (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ normalizer (L : Set G))
    (X : Subgroup G) (hX : IsMaximalTwoLocal X) (hLX : L ⊔ (S : Subgroup G) ≤ X) :
    X = normalizer (L : Set G) := by
  let M := normalizer (L : Set G)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M (T.subtype d.normalizes_L) (S.subtype hS)
  rw [Sylow.smul_subtype] at hg
  have hTS := congrArg Sylow.toSubgroup (Sylow.subtype_injective hg)
  let a : G ≃* G := MulAut.conj (g : G)
  change (T : Subgroup G).map a.toMonoidHom = (S : Subgroup G) at hTS
  have hL : L.map a.toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp g.property
  have hM : M.map a.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  have hcancel : a.symm.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
    ext x
    exact a.symm_apply_apply x
  have hcancel' : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id G := by
    ext x
    exact a.apply_symm_apply x
  have hh : L ⊔ (T : Subgroup G) ≤ X.map a.symm.toMonoidHom := by
    have hm : (L ⊔ (T : Subgroup G)).map a.toMonoidHom ≤ X := by
      rwa [Subgroup.map_sup,hL,hTS]
    simpa only [map_map,hcancel,map_id] using
      (map_mono (f := a.symm.toMonoidHom) hm)
  have he := d.unique_maximal_overgroup _ (Theory.Quasithin.isMaximalTwoLocal_map a.symm hX) hh
  change X.map a.symm.toMonoidHom = M at he
  have hm := congrArg (fun Y : Subgroup G => Y.map a.toMonoidHom) he
  simpa only [map_map,hcancel',map_id,hM] using hm

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
