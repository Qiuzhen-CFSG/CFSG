module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockData

/-! Kernel certificates for four-letter products, batch 3. See BlockData. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem block57_spec : ∀ x : Fin 6156,
    lookup packed57 x.val = (evalWord gen [4, 5, 6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed57 x.val = ev rawGen [4, 5, 6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block58_spec : ∀ x : Fin 6156,
    lookup packed58 x.val = (evalWord gen [5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed58 x.val = ev rawGen [5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block59_spec : ∀ x : Fin 6156,
    lookup packed59 x.val = (evalWord gen [5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed59 x.val = ev rawGen [5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block60_spec : ∀ x : Fin 6156,
    lookup packed60 x.val = (evalWord gen [5, 4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed60 x.val = ev rawGen [5, 4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block61_spec : ∀ x : Fin 6156,
    lookup packed61 x.val = (evalWord gen [5, 4, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed61 x.val = ev rawGen [5, 4, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block62_spec : ∀ x : Fin 6156,
    lookup packed62 x.val = (evalWord gen [5, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed62 x.val = ev rawGen [5, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block63_spec : ∀ x : Fin 6156,
    lookup packed63 x.val = (evalWord gen [5, 4, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed63 x.val = ev rawGen [5, 4, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block64_spec : ∀ x : Fin 6156,
    lookup packed64 x.val = (evalWord gen [5, 4, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed64 x.val = ev rawGen [5, 4, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block65_spec : ∀ x : Fin 6156,
    lookup packed65 x.val = (evalWord gen [5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed65 x.val = ev rawGen [5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block66_spec : ∀ x : Fin 6156,
    lookup packed66 x.val = (evalWord gen [5, 6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed66 x.val = ev rawGen [5, 6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block67_spec : ∀ x : Fin 6156,
    lookup packed67 x.val = (evalWord gen [5, 6, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed67 x.val = ev rawGen [5, 6, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block68_spec : ∀ x : Fin 6156,
    lookup packed68 x.val = (evalWord gen [5, 6, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed68 x.val = ev rawGen [5, 6, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block69_spec : ∀ x : Fin 6156,
    lookup packed69 x.val = (evalWord gen [6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed69 x.val = ev rawGen [6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block70_spec : ∀ x : Fin 6156,
    lookup packed70 x.val = (evalWord gen [6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed70 x.val = ev rawGen [6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block71_spec : ∀ x : Fin 6156,
    lookup packed71 x.val = (evalWord gen [6, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed71 x.val = ev rawGen [6, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block72_spec : ∀ x : Fin 6156,
    lookup packed72 x.val = (evalWord gen [6, 5, 4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed72 x.val = ev rawGen [6, 5, 4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block73_spec : ∀ x : Fin 6156,
    lookup packed73 x.val = (evalWord gen [6, 5, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed73 x.val = ev rawGen [6, 5, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block74_spec : ∀ x : Fin 6156,
    lookup packed74 x.val = (evalWord gen [6, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed74 x.val = ev rawGen [6, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block75_spec : ∀ x : Fin 6156,
    lookup packed75 x.val = (evalWord gen [6, 5, 6, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed75 x.val = ev rawGen [6, 5, 6, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
