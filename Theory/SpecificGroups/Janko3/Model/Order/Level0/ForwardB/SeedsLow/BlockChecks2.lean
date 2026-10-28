module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockData

/-! Kernel certificates for four-letter products, batch 2. See BlockData. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

set_option maxRecDepth 40000 in
public theorem block38_spec : ∀ x : Fin 6156,
    lookup packed38 x.val = (evalWord gen [1, 0, 1, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed38 x.val = ev rawGen [1, 0, 1, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block39_spec : ∀ x : Fin 6156,
    lookup packed39 x.val = (evalWord gen [1, 0, 3] x).val := by
  have h : ∀ x : Fin 6156, lookup packed39 x.val = ev rawGen [1, 0, 3] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block40_spec : ∀ x : Fin 6156,
    lookup packed40 x.val = (evalWord gen [1, 0, 3, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed40 x.val = ev rawGen [1, 0, 3, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block41_spec : ∀ x : Fin 6156,
    lookup packed41 x.val = (evalWord gen [3] x).val := by
  have h : ∀ x : Fin 6156, lookup packed41 x.val = ev rawGen [3] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block42_spec : ∀ x : Fin 6156,
    lookup packed42 x.val = (evalWord gen [3, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed42 x.val = ev rawGen [3, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block43_spec : ∀ x : Fin 6156,
    lookup packed43 x.val = (evalWord gen [3, 0, 1] x).val := by
  have h : ∀ x : Fin 6156, lookup packed43 x.val = ev rawGen [3, 0, 1] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block44_spec : ∀ x : Fin 6156,
    lookup packed44 x.val = (evalWord gen [3, 0, 1, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed44 x.val = ev rawGen [3, 0, 1, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block45_spec : ∀ x : Fin 6156,
    lookup packed45 x.val = (evalWord gen [3, 0, 3] x).val := by
  have h : ∀ x : Fin 6156, lookup packed45 x.val = ev rawGen [3, 0, 3] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block46_spec : ∀ x : Fin 6156,
    lookup packed46 x.val = (evalWord gen [3, 0, 3, 0] x).val := by
  have h : ∀ x : Fin 6156, lookup packed46 x.val = ev rawGen [3, 0, 3, 0] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block47_spec : ∀ x : Fin 6156,
    lookup packed47 x.val = (evalWord gen [4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed47 x.val = ev rawGen [4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block48_spec : ∀ x : Fin 6156,
    lookup packed48 x.val = (evalWord gen [4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed48 x.val = ev rawGen [4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block49_spec : ∀ x : Fin 6156,
    lookup packed49 x.val = (evalWord gen [4, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed49 x.val = ev rawGen [4, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block50_spec : ∀ x : Fin 6156,
    lookup packed50 x.val = (evalWord gen [4, 4, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed50 x.val = ev rawGen [4, 4, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block51_spec : ∀ x : Fin 6156,
    lookup packed51 x.val = (evalWord gen [4, 4, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed51 x.val = ev rawGen [4, 4, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block52_spec : ∀ x : Fin 6156,
    lookup packed52 x.val = (evalWord gen [4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed52 x.val = ev rawGen [4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block53_spec : ∀ x : Fin 6156,
    lookup packed53 x.val = (evalWord gen [4, 5, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed53 x.val = ev rawGen [4, 5, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block54_spec : ∀ x : Fin 6156,
    lookup packed54 x.val = (evalWord gen [4, 5, 4, 4] x).val := by
  have h : ∀ x : Fin 6156, lookup packed54 x.val = ev rawGen [4, 5, 4, 4] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block55_spec : ∀ x : Fin 6156,
    lookup packed55 x.val = (evalWord gen [4, 5, 4, 5] x).val := by
  have h : ∀ x : Fin 6156, lookup packed55 x.val = ev rawGen [4, 5, 4, 5] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

set_option maxRecDepth 40000 in
public theorem block56_spec : ∀ x : Fin 6156,
    lookup packed56 x.val = (evalWord gen [4, 5, 6] x).val := by
  have h : ∀ x : Fin 6156, lookup packed56 x.val = ev rawGen [4, 5, 6] x.val := by
    apply allFin
    decide +kernel
  simpa only [ev_spec rawGen gen rawGen_spec] using h

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
